#include "nlisp.h"

#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { size_t line, column; } Span;
typedef struct {
    bool set;
    NLispStatus status;
    Span span;
    char message[512];
} Error;

static bool fail(Error *e, NLispStatus status, Span span, const char *fmt, ...) {
    va_list ap;
    if (e->set) return false;
    e->set = true; e->status = status; e->span = span;
    va_start(ap, fmt);
    (void)vsnprintf(e->message, sizeof(e->message), fmt, ap);
    va_end(ap);
    return false;
}

typedef struct Allocation { void *ptr; struct Allocation *next; } Allocation;
struct Type;
struct Macro;
typedef struct {
    Allocation *head;
    struct Type **type_variables;
    size_t type_variable_count;
    struct Macro *macros;
    size_t fresh_scope;
} Arena;

static void *aalloc(Arena *a, size_t n) {
    void *p;
    Allocation *x;
    if (n == 0U) n = 1U;
    p = calloc(1U, n);
    x = (Allocation *)malloc(sizeof(*x));
    if (p == NULL || x == NULL) {
        free(p); free(x); fputs("nlisp: out of memory\n", stderr); abort();
    }
    x->ptr = p; x->next = a->head; a->head = x;
    return p;
}

static char *astr(Arena *a, const char *s, size_t n) {
    char *r = (char *)aalloc(a, n + 1U);
    if (n != 0U) memcpy(r, s, n);
    r[n] = '\0';
    return r;
}

static void adestroy(Arena *a) {
    Allocation *x = a->head;
    while (x != NULL) {
        Allocation *next = x->next;
        free(x->ptr); free(x); x = next;
    }
    a->head = NULL;
}

typedef enum { TK_LEFT, TK_RIGHT, TK_ATOM, TK_END } TokenKind;
typedef struct { TokenKind kind; Span span; char *text; } Token;
typedef struct { Token *data; size_t count; } Tokens;

static bool delimiter(char c) {
    return c == '(' || c == ')' || c == ';' || isspace((unsigned char)c) != 0;
}

static bool lex(Arena *a, const char *src, size_t len, Tokens *out, Error *e) {
    size_t i = 0U, line = 1U, col = 1U, count = 0U;
    Token *ts = (Token *)aalloc(a, (len + 1U) * sizeof(*ts));
    while (i < len) {
        char c = src[i];
        if (c == '\r' || c == '\n') {
            if (c == '\r' && i + 1U < len && src[i + 1U] == '\n') i++;
            i++; line++; col = 1U; continue;
        }
        if (isspace((unsigned char)c) != 0) { i++; col++; continue; }
        if (c == ';') {
            while (i < len && src[i] != '\r' && src[i] != '\n') { i++; col++; }
            continue;
        }
        if (c == '(' || c == ')') {
            ts[count++] = (Token){c == '(' ? TK_LEFT : TK_RIGHT, {line, col}, NULL};
            i++; col++; continue;
        }
        if (c == '"')
            return fail(e, NLISP_PARSE_ERROR, (Span){line, col},
                        "string literals are not implemented in NLisp-Core");
        {
            size_t start = i, start_col = col;
            while (i < len && !delimiter(src[i])) { i++; col++; }
            if (i - start >= 7U && strncmp(src + start, "#%nlisp", 7U) == 0)
                return fail(e, NLISP_PARSE_ERROR, (Span){line, start_col}, "reserved generated identifier prefix");
            ts[count++] = (Token){TK_ATOM, {line, start_col}, astr(a, src + start, i - start)};
        }
    }
    ts[count++] = (Token){TK_END, {line, col}, NULL};
    out->data = ts; out->count = count;
    return true;
}

typedef enum { SX_ATOM, SX_LIST } SKind;
typedef struct SExpr {
    SKind kind; Span span; char *atom;
    struct SExpr **items; size_t count;
    void *checked_parameters;
    size_t checked_arity;
    struct SExpr *expanded;
    struct Macro *origin;
} SExpr;
typedef struct SNode { SExpr *value; struct SNode *next; } SNode;
typedef struct { Arena *a; Tokens ts; size_t pos; Error *e; } Parser;

static SExpr *parse_expr(Parser *p);

static SExpr *parse_list(Parser *p, Span span) {
    SNode *first = NULL, *last = NULL, *node;
    size_t n = 0U, i = 0U;
    SExpr *r;
    p->pos++;
    while (p->ts.data[p->pos].kind != TK_RIGHT) {
        SExpr *v;
        if (p->ts.data[p->pos].kind == TK_END) {
            (void)fail(p->e, NLISP_PARSE_ERROR, span, "unterminated list");
            return NULL;
        }
        v = parse_expr(p);
        if (v == NULL) return NULL;
        node = (SNode *)aalloc(p->a, sizeof(*node)); node->value = v;
        if (last == NULL) first = node; else last->next = node;
        last = node; n++;
    }
    p->pos++;
    r = (SExpr *)aalloc(p->a, sizeof(*r));
    r->kind = SX_LIST; r->span = span; r->count = n;
    r->items = (SExpr **)aalloc(p->a, n * sizeof(*r->items));
    for (node = first; node != NULL; node = node->next) r->items[i++] = node->value;
    return r;
}

static SExpr *parse_expr(Parser *p) {
    Token t = p->ts.data[p->pos];
    SExpr *r;
    if (t.kind == TK_LEFT) return parse_list(p, t.span);
    if (t.kind == TK_RIGHT) {
        (void)fail(p->e, NLISP_PARSE_ERROR, t.span, "unexpected ')'");
        return NULL;
    }
    if (t.kind == TK_END) {
        (void)fail(p->e, NLISP_PARSE_ERROR, t.span, "unexpected end of input");
        return NULL;
    }
    p->pos++;
    r = (SExpr *)aalloc(p->a, sizeof(*r));
    r->kind = SX_ATOM; r->span = t.span; r->atom = t.text;
    return r;
}

typedef struct { SExpr **data; size_t count; } Forms;

static bool parse_forms(Arena *a, Tokens ts, Forms *out, Error *e) {
    Parser p = {a, ts, 0U, e};
    SNode *first = NULL, *last = NULL, *node;
    size_t n = 0U, i = 0U;
    while (p.ts.data[p.pos].kind != TK_END) {
        SExpr *v = parse_expr(&p);
        if (v == NULL) return false;
        node = (SNode *)aalloc(a, sizeof(*node)); node->value = v;
        if (last == NULL) first = node; else last->next = node;
        last = node; n++;
    }
    out->data = (SExpr **)aalloc(a, n * sizeof(*out->data)); out->count = n;
    for (node = first; node != NULL; node = node->next) out->data[i++] = node->value;
    return true;
}

static bool is_atom(const SExpr *x, const char *s) {
    return x->kind == SX_ATOM && strcmp(x->atom, s) == 0;
}

typedef enum { TY_BOOL, TY_INT, TY_UNIT, TY_FUN, TY_LIST, TY_OPTION, TY_VAR, TY_FORALL } TypeKind;
typedef struct Type {
    TypeKind kind;
    struct Type *elem;
    struct Type **params;
    size_t arity;
    struct Type *result;
    const char *name;
    struct Type **variables;
    size_t variable_count;
} Type;

static Type *type_new(Arena *a, TypeKind k) {
    Type *t = (Type *)aalloc(a, sizeof(*t)); t->kind = k; return t;
}

static Type *type_fun(Arena *a, Type **ps, size_t n, Type *r) {
    Type *t = type_new(a, TY_FUN); t->params = ps; t->arity = n; t->result = r; return t;
}

static Type *parse_type(Arena *a, const SExpr *x, Error *e) {
    Type *t;
    if (x->kind == SX_ATOM) {
        size_t i;
        if (strcmp(x->atom, "Boolean") == 0) return type_new(a, TY_BOOL);
        if (strcmp(x->atom, "Integer") == 0) return type_new(a, TY_INT);
        if (strcmp(x->atom, "Unit") == 0) return type_new(a, TY_UNIT);
        for (i = 0U; i < a->type_variable_count; i++)
            if (strcmp(a->type_variables[i]->name, x->atom) == 0) return a->type_variables[i];
        (void)fail(e, NLISP_PARSE_ERROR, x->span, "unknown or unsupported type '%s'", x->atom);
        return NULL;
    }
    if (x->count == 2U && (is_atom(x->items[0], "List") || is_atom(x->items[0], "Option"))) {
        t = type_new(a, is_atom(x->items[0], "List") ? TY_LIST : TY_OPTION);
        t->elem = parse_type(a, x->items[1], e);
        return t->elem == NULL ? NULL : t;
    }
    if (x->count == 3U && is_atom(x->items[0], "Function") && x->items[1]->kind == SX_LIST) {
        const SExpr *args = x->items[1];
        Type **ps = (Type **)aalloc(a, args->count * sizeof(*ps));
        size_t i;
        for (i = 0U; i < args->count; i++) {
            ps[i] = parse_type(a, args->items[i], e);
            if (ps[i] == NULL) return NULL;
        }
        t = parse_type(a, x->items[2], e);
        return t == NULL ? NULL : type_fun(a, ps, args->count, t);
    }
    (void)fail(e, NLISP_PARSE_ERROR, x->span, "invalid type expression");
    return NULL;
}

static bool type_eq(const Type *a, const Type *b) {
    size_t i;
    if (a->kind != b->kind) return false;
    switch (a->kind) {
        case TY_VAR: return a == b;
        case TY_FORALL: return a == b;
        case TY_BOOL: case TY_INT: case TY_UNIT: return true;
        case TY_LIST: case TY_OPTION: return type_eq(a->elem, b->elem);
        case TY_FUN:
            if (a->arity != b->arity) return false;
            for (i = 0U; i < a->arity; i++) if (!type_eq(a->params[i], b->params[i])) return false;
            return type_eq(a->result, b->result);
    }
    return false;
}

static void type_text(const Type *t, char *buf, size_t size) {
    const char *name = NULL;
    size_t used = 0U, i;
    int n;
    if (size == 0U) return;
    buf[0] = '\0';
    switch (t->kind) {
        case TY_VAR: name = t->name; break;
        case TY_FORALL:
            (void)snprintf(buf, size, "(forall (...) ...)");
            return;
        case TY_BOOL: name = "Boolean"; break;
        case TY_INT: name = "Integer"; break;
        case TY_UNIT: name = "Unit"; break;
        case TY_LIST: case TY_OPTION: {
            char sub[160];
            type_text(t->elem, sub, sizeof(sub));
            (void)snprintf(buf, size, "(%s %s)", t->kind == TY_LIST ? "List" : "Option", sub);
            return;
        }
        case TY_FUN:
            n = snprintf(buf, size, "(Function ("); used = n > 0 ? (size_t)n : 0U;
            for (i = 0U; i < t->arity && used < size; i++) {
                char sub[160]; type_text(t->params[i], sub, sizeof(sub));
                n = snprintf(buf + used, size - used, "%s%s", i == 0U ? "" : " ", sub);
                if (n > 0) used += (size_t)n;
            }
            if (used < size) {
                char sub[160]; type_text(t->result, sub, sizeof(sub));
                (void)snprintf(buf + used, size - used, ") %s)", sub);
            }
            return;
    }
    if (name != NULL) (void)snprintf(buf, size, "%s", name);
}

typedef struct { char *name; Type *type; Span span; } Param;
typedef struct {
    char *name; Param *params; size_t arity;
    Type *ret, *type; SExpr *body; Span span;
} FunDef;
typedef struct { char *name; Type *type; SExpr *init; Span span; } ValDef;
typedef enum { D_FUN, D_VAL } DeclKind;
typedef struct { DeclKind kind; union { FunDef fun; ValDef val; } as; } Decl;
typedef struct { Decl *data; size_t count; } Program;

static bool parse_params(Arena *a, const SExpr *x, Param **out, size_t *count, Error *e) {
    Param *ps;
    size_t i, j;
    if (x->kind != SX_LIST) return fail(e, NLISP_PARSE_ERROR, x->span, "expected parameter list");
    ps = (Param *)aalloc(a, x->count * sizeof(*ps));
    for (i = 0U; i < x->count; i++) {
        const SExpr *p = x->items[i];
        if (p->kind != SX_LIST || p->count != 2U || p->items[0]->kind != SX_ATOM)
            return fail(e, NLISP_PARSE_ERROR, p->span, "parameter must have form (name Type)");
        for (j = 0U; j < i; j++)
            if (strcmp(ps[j].name, p->items[0]->atom) == 0)
                return fail(e, NLISP_PARSE_ERROR, p->span, "duplicate parameter '%s'", p->items[0]->atom);
        ps[i].name = p->items[0]->atom; ps[i].span = p->items[0]->span;
        ps[i].type = parse_type(a, p->items[1], e);
        if (ps[i].type == NULL) return false;
    }
    *out = ps; *count = x->count; return true;
}

static bool parse_program(Arena *a, Forms forms, Program *out, Error *e) {
    size_t i, j;
    Decl *ds = (Decl *)aalloc(a, forms.count * sizeof(*ds));
    for (i = 0U; i < forms.count; i++) {
        SExpr *f = forms.data[i];
        if (f->kind != SX_LIST || f->count == 0U || f->items[0]->kind != SX_ATOM)
            return fail(e, NLISP_PARSE_ERROR, f->span, "top-level form must be a declaration");
        if (is_atom(f->items[0], "defun")) {
            FunDef *d; Type **ps;
            const SExpr *args, *ret, *body, *quantifiers = NULL;
            Type **variables = NULL;
            size_t variable_count = 0U;
            if ((f->count != 5U && f->count != 4U) || f->items[1]->kind != SX_ATOM)
                return fail(e, NLISP_PARSE_ERROR, f->span,
                            "defun form is (defun name ((arg Type) ...) ReturnType body)");
            ds[i].kind = D_FUN; d = &ds[i].as.fun;
            d->name = f->items[1]->atom; d->span = f->items[1]->span;
            if (f->count == 4U) {
                const SExpr *signature = f->items[2];
                if (signature->kind != SX_LIST || signature->count != 4U ||
                    !is_atom(signature->items[0], "forall") ||
                    signature->items[1]->kind != SX_LIST || signature->items[1]->count == 0U)
                    return fail(e, NLISP_PARSE_ERROR, signature->span, "expected (forall (T ...) ((arg Type) ...) ReturnType)");
                quantifiers = signature->items[1];
                variable_count = quantifiers->count;
                variables = (Type **)aalloc(a, variable_count * sizeof(*variables));
                for (j = 0U; j < variable_count; j++) {
                    size_t k;
                    const SExpr *q = quantifiers->items[j];
                    if (q->kind != SX_ATOM || is_atom(q, "Boolean") || is_atom(q, "Integer") ||
                        is_atom(q, "Unit") || is_atom(q, "List") || is_atom(q, "Option") ||
                        is_atom(q, "Function") || is_atom(q, "forall") || is_atom(q, "Syntax"))
                        return fail(e, NLISP_PARSE_ERROR, q->span, "invalid type variable");
                    for (k = 0U; k < j; k++)
                        if (strcmp(variables[k]->name, q->atom) == 0)
                            return fail(e, NLISP_PARSE_ERROR, q->span, "duplicate type variable '%s'", q->atom);
                    variables[j] = type_new(a, TY_VAR); variables[j]->name = q->atom;
                }
                args = signature->items[2]; ret = signature->items[3]; body = f->items[3];
            } else {
                args = f->items[2]; ret = f->items[3]; body = f->items[4];
            }
            a->type_variables = variables; a->type_variable_count = variable_count;
            if (!parse_params(a, args, &d->params, &d->arity, e)) return false;
            d->ret = parse_type(a, ret, e); if (d->ret == NULL) return false;
            ps = (Type **)aalloc(a, d->arity * sizeof(*ps));
            for (j = 0U; j < d->arity; j++) ps[j] = d->params[j].type;
            d->type = type_fun(a, ps, d->arity, d->ret); d->body = (SExpr *)body;
            if (variable_count != 0U) {
                Type *scheme = type_new(a, TY_FORALL);
                scheme->result = d->type; scheme->variables = variables;
                scheme->variable_count = variable_count; d->type = scheme;
            }
            a->type_variables = NULL; a->type_variable_count = 0U;
        } else if (is_atom(f->items[0], "define")) {
            ValDef *d; const SExpr *b;
            if (f->count != 3U || f->items[1]->kind != SX_LIST || f->items[1]->count != 2U ||
                f->items[1]->items[0]->kind != SX_ATOM)
                return fail(e, NLISP_PARSE_ERROR, f->span,
                            "define form is (define (name Type) expression)");
            ds[i].kind = D_VAL; d = &ds[i].as.val; b = f->items[1];
            d->name = b->items[0]->atom; d->span = b->items[0]->span;
            d->type = parse_type(a, b->items[1], e); if (d->type == NULL) return false;
            d->init = f->items[2];
        } else return fail(e, NLISP_PARSE_ERROR, f->items[0]->span,
                           "unknown top-level declaration '%s'", f->items[0]->atom);
    }
    out->data = ds; out->count = forms.count; return true;
}

typedef struct TBind { const char *name; Type *type; struct TBind *next; } TBind;
static Type *tlookup(TBind *env, const char *name) {
    for (; env != NULL; env = env->next) if (strcmp(env->name, name) == 0) return env->type;
    return NULL;
}
static TBind *tbind(Arena *a, TBind *env, const char *name, Type *type) {
    TBind *b = (TBind *)aalloc(a, sizeof(*b)); b->name = name; b->type = type; b->next = env; return b;
}

struct RBind;
typedef struct Macro {
    const char *name;
    SExpr *pattern, *contracts, *template_expr;
    Type **inputs, *output;
    size_t arity, declaration_index;
    TBind *type_env;
    struct RBind *runtime_env;
    struct Macro *next;
    bool checking;
} Macro;

/* Fixed-arity rules, monomorphic contracts, and references only to earlier
   macros make template expansion finite. */
static bool collect_macros(Arena *a, Forms *forms, Error *e) {
    size_t i, count = 0U;
    for (i = 0U; i < forms->count; i++) {
        SExpr *form = forms->data[i];
        if (form->kind == SX_LIST && form->count > 0U &&
            is_atom(form->items[0], "define-macro")) {
            SExpr *rules, *rule, *pattern, *contracts, *output;
            Macro *m, *previous;
            size_t j, k;
            if (form->count != 3U || form->items[1]->kind != SX_ATOM ||
                form->items[2]->kind != SX_LIST)
                return fail(e, NLISP_PARSE_ERROR, form->span, "invalid define-macro");
            rules = form->items[2];
            if (rules->count != 2U || !is_atom(rules->items[0], "syntax-rules/typed"))
                return fail(e, NLISP_PARSE_ERROR, rules->span,
                            "initial macro implementation requires one syntax-rules/typed rule");
            rule = rules->items[1];
            if (rule->kind != SX_LIST || rule->count != 4U)
                return fail(e, NLISP_PARSE_ERROR, rule->span, "invalid typed macro rule");
            pattern = rule->items[0]; contracts = rule->items[1]; output = rule->items[2];
            if (pattern->kind != SX_LIST || pattern->count == 0U ||
                !is_atom(pattern->items[0], form->items[1]->atom) ||
                contracts->kind != SX_LIST || contracts->count != pattern->count - 1U ||
                output->kind != SX_LIST || output->count != 2U ||
                !is_atom(output->items[0], "Syntax"))
                return fail(e, NLISP_PARSE_ERROR, rule->span, "invalid macro pattern or Syntax contract");
            for (previous = a->macros; previous != NULL; previous = previous->next)
                if (strcmp(previous->name, form->items[1]->atom) == 0)
                    return fail(e, NLISP_TYPE_ERROR, form->span, "duplicate macro name");
            m = (Macro *)aalloc(a, sizeof(*m));
            m->name = form->items[1]->atom; m->pattern = pattern; m->contracts = contracts;
            m->template_expr = rule->items[3]; m->arity = contracts->count;
            m->declaration_index = count;
            m->inputs = (Type **)aalloc(a, m->arity * sizeof(*m->inputs));
            for (j = 0U; j < m->arity; j++) {
                SExpr *c = contracts->items[j];
                if (pattern->items[j + 1U]->kind != SX_ATOM ||
                    c->kind != SX_LIST || c->count != 2U ||
                    !is_atom(c->items[0], pattern->items[j + 1U]->atom) ||
                    c->items[1]->kind != SX_LIST || c->items[1]->count != 2U ||
                    !is_atom(c->items[1]->items[0], "Syntax"))
                    return fail(e, NLISP_PARSE_ERROR, c->span, "input contract must be (parameter (Syntax Type)) in pattern order");
                for (k = 0U; k < j; k++)
                    if (strcmp(pattern->items[k + 1U]->atom, pattern->items[j + 1U]->atom) == 0)
                        return fail(e, NLISP_PARSE_ERROR, c->span, "duplicate macro parameter");
                m->inputs[j] = parse_type(a, c->items[1]->items[1], e);
                if (m->inputs[j] == NULL) return false;
            }
            m->output = parse_type(a, output->items[1], e);
            if (m->output == NULL) return false;
            m->next = a->macros; a->macros = m;
        } else forms->data[count++] = form;
    }
    forms->count = count;
    return true;
}

typedef struct Rename {
    const char *from;
    char *to;
    struct Rename *next;
} Rename;

static bool macro_parameter(Macro *m, const char *name, size_t *index) {
    size_t i;
    for (i = 0U; i < m->arity; i++) if (strcmp(m->pattern->items[i + 1U]->atom, name) == 0) {
        *index = i; return true;
    }
    return false;
}

static SExpr *copy_template(Arena *a, Macro *m, SExpr *x, SExpr **args, Rename *renames, Error *e);

static SExpr *copy_binder(Arena *a, Macro *m, SExpr *x, Rename **renames, Error *e) {
    SExpr *r;
    Rename *name;
    size_t ignored;
    char buffer[80];
    if (x->kind != SX_ATOM || macro_parameter(m, x->atom, &ignored)) {
        (void)fail(e, NLISP_PARSE_ERROR, x->span, "macro holes cannot occur in binding positions");
        return NULL;
    }
    r = (SExpr *)aalloc(a, sizeof(*r)); *r = *x;
    (void)snprintf(buffer, sizeof(buffer), "#%%nlisp%zu", ++a->fresh_scope);
    r->atom = astr(a, buffer, strlen(buffer));
    name = (Rename *)aalloc(a, sizeof(*name));
    name->from = x->atom; name->to = r->atom; name->next = *renames; *renames = name;
    return r;
}

static SExpr *copy_template(Arena *a, Macro *m, SExpr *x, SExpr **args, Rename *renames, Error *e) {
    SExpr *r;
    size_t i, index;
    Rename *name;
    if (x->kind == SX_ATOM) {
        for (name = renames; name != NULL; name = name->next) if (strcmp(name->from, x->atom) == 0) {
            r = (SExpr *)aalloc(a, sizeof(*r)); *r = *x; r->atom = name->to; return r;
        }
        if (macro_parameter(m, x->atom, &index)) return args[index];
        r = (SExpr *)aalloc(a, sizeof(*r)); *r = *x; r->origin = m; return r;
    }
    r = (SExpr *)aalloc(a, sizeof(*r)); *r = *x;
    r->items = (SExpr **)aalloc(a, x->count * sizeof(*r->items));
    for (i = 0U; i < x->count; i++) r->items[i] = x->items[i];
    if (x->count == 4U && is_atom(x->items[0], "lambda") && x->items[1]->kind == SX_LIST) {
        SExpr *ps = (SExpr *)aalloc(a, sizeof(*ps)); *ps = *x->items[1];
        ps->items = (SExpr **)aalloc(a, ps->count * sizeof(*ps->items));
        for (i = 0U; i < ps->count; i++) {
            SExpr *p = x->items[1]->items[i], *q;
            if (p->kind != SX_LIST || p->count != 2U) {
                (void)fail(e, NLISP_PARSE_ERROR, p->span, "invalid template lambda parameter"); return NULL;
            }
            q = (SExpr *)aalloc(a, sizeof(*q)); *q = *p;
            q->items = (SExpr **)aalloc(a, 2U * sizeof(*q->items));
            q->items[0] = copy_binder(a, m, p->items[0], &renames, e); q->items[1] = p->items[1];
            if (q->items[0] == NULL) return NULL;
            ps->items[i] = q;
        }
        r->items[1] = ps;
        r->items[3] = copy_template(a, m, x->items[3], args, renames, e);
        return r->items[3] == NULL ? NULL : r;
    }
    if (x->count == 3U && is_atom(x->items[0], "let") && x->items[1]->kind == SX_LIST) {
        SExpr *bs = (SExpr *)aalloc(a, sizeof(*bs)); Rename *body_names = renames;
        *bs = *x->items[1]; bs->items = (SExpr **)aalloc(a, bs->count * sizeof(*bs->items));
        for (i = 0U; i < bs->count; i++) {
            SExpr *b = x->items[1]->items[i], *q, *d;
            if (b->kind != SX_LIST || b->count != 2U || b->items[0]->kind != SX_LIST || b->items[0]->count != 2U) {
                (void)fail(e, NLISP_PARSE_ERROR, b->span, "invalid template let binding"); return NULL;
            }
            q = (SExpr *)aalloc(a, sizeof(*q)); *q = *b;
            q->items = (SExpr **)aalloc(a, 2U * sizeof(*q->items));
            d = (SExpr *)aalloc(a, sizeof(*d)); *d = *b->items[0];
            d->items = (SExpr **)aalloc(a, 2U * sizeof(*d->items));
            d->items[0] = copy_binder(a, m, b->items[0]->items[0], &body_names, e);
            d->items[1] = b->items[0]->items[1];
            q->items[0] = d; q->items[1] = copy_template(a, m, b->items[1], args, renames, e);
            if (d->items[0] == NULL || q->items[1] == NULL) return NULL;
            bs->items[i] = q;
        }
        r->items[1] = bs;
        r->items[2] = copy_template(a, m, x->items[2], args, body_names, e);
        return r->items[2] == NULL ? NULL : r;
    }
    if (x->count >= 3U && is_atom(x->items[0], "match")) {
        r->items[1] = copy_template(a, m, x->items[1], args, renames, e);
        if (r->items[1] == NULL) return NULL;
        for (i = 2U; i < x->count; i++) {
            SExpr *c = x->items[i], *q, *p; size_t j; Rename *local = renames;
            if (c->kind != SX_LIST || c->count != 2U || c->items[0]->kind != SX_LIST) {
                (void)fail(e, NLISP_PARSE_ERROR, c->span, "invalid template match clause"); return NULL;
            }
            q = (SExpr *)aalloc(a, sizeof(*q)); *q = *c;
            q->items = (SExpr **)aalloc(a, 2U * sizeof(*q->items));
            p = (SExpr *)aalloc(a, sizeof(*p)); *p = *c->items[0];
            p->items = (SExpr **)aalloc(a, p->count * sizeof(*p->items));
            if (p->count > 0U) p->items[0] = c->items[0]->items[0];
            for (j = 1U; j < p->count; j++) {
                p->items[j] = copy_binder(a, m, c->items[0]->items[j], &local, e);
                if (p->items[j] == NULL) return NULL;
            }
            q->items[0] = p; q->items[1] = copy_template(a, m, c->items[1], args, local, e);
            if (q->items[1] == NULL) return NULL;
            r->items[i] = q;
        }
        return r;
    }
    for (i = 0U; i < x->count; i++) {
        r->items[i] = copy_template(a, m, x->items[i], args, renames, e);
        if (r->items[i] == NULL) return NULL;
    }
    return r;
}

static bool integer_atom(const char *s, int64_t *out) {
    char *end = NULL; long long v;
    if (*s == '\0') return false;
    errno = 0; v = strtoll(s, &end, 10);
    if (errno == ERANGE || end == s || *end != '\0') return false;
    *out = (int64_t)v; return true;
}

static bool require(const Type *got, const Type *want, Span span, Error *e, const char *where) {
    char a[256], b[256];
    if (type_eq(got, want)) return true;
    type_text(got, a, sizeof(a)); type_text(want, b, sizeof(b));
    return fail(e, NLISP_TYPE_ERROR, span, "%s: expected %s, got %s", where, b, a);
}

static Type *check_expr(Arena *a, const SExpr *x, TBind *env, Error *e);

static Type *check_macro_call(Arena *a, const SExpr *x, Macro *m, TBind *env, Error *e) {
    size_t i;
    Type *got;
    SExpr *expanded;
    if (m->checking) {
        (void)fail(e, NLISP_TYPE_ERROR, x->span, "recursive macro expansion is forbidden"); return NULL;
    }
    if (x->count - 1U != m->arity) {
        (void)fail(e, NLISP_TYPE_ERROR, x->span, "macro '%s' expects %zu arguments", m->name, m->arity); return NULL;
    }
    for (i = 0U; i < m->arity; i++) {
        got = check_expr(a, x->items[i + 1U], env, e);
        if (got == NULL || !require(got, m->inputs[i], x->items[i + 1U]->span, e, "macro input contract"))
            return NULL;
    }
    expanded = copy_template(a, m, m->template_expr, x->items + 1U, NULL, e);
    if (expanded == NULL) return NULL;
    m->checking = true;
    got = check_expr(a, expanded, env, e);
    m->checking = false;
    if (got == NULL || !require(got, m->output, x->span, e, "macro output contract")) return NULL;
    ((SExpr *)x)->expanded = expanded;
    return got;
}

static bool prepare_macros(Arena *a, Macro *m, size_t index, TBind *env, Error *e) {
    SExpr **holes, *template_expr;
    TBind *local = env;
    Type *got;
    size_t i;
    if (m == NULL) return true;
    if (!prepare_macros(a, m->next, index, env, e)) return false;
    if (m->declaration_index != index) return true;
    if (tlookup(env, m->name) != NULL)
        return fail(e, NLISP_TYPE_ERROR, m->pattern->span, "macro name conflicts with value '%s'", m->name);
    holes = (SExpr **)aalloc(a, m->arity * sizeof(*holes));
    for (i = 0U; i < m->arity; i++) {
        holes[i] = m->pattern->items[i + 1U];
        local = tbind(a, local, holes[i]->atom, m->inputs[i]);
    }
    m->type_env = env;
    template_expr = copy_template(a, m, m->template_expr, holes, NULL, e);
    if (template_expr == NULL) return false;
    m->checking = true;
    got = check_expr(a, template_expr, local, e);
    m->checking = false;
    return got != NULL && require(got, m->output, m->template_expr->span, e, "macro definition output");
}

/* Only the callee's quantified variables are flexible. Variables belonging
   to the caller remain rigid, even when their printed names coincide. */
static bool monotype(const Type *t) {
    size_t i;
    if (t->kind == TY_FORALL) return false;
    if (t->kind == TY_LIST || t->kind == TY_OPTION) return monotype(t->elem);
    if (t->kind == TY_FUN) {
        for (i = 0U; i < t->arity; i++) if (!monotype(t->params[i])) return false;
        return monotype(t->result);
    }
    return true;
}

static bool match_type(Type *pattern, Type *actual, Type *scheme, Type **sub) {
    size_t i;
    if (!monotype(actual)) return false;
    for (i = 0U; i < scheme->variable_count; i++) if (pattern == scheme->variables[i]) {
        if (sub[i] == NULL) { sub[i] = actual; return true; }
        return type_eq(sub[i], actual);
    }
    if (pattern->kind != actual->kind) return false;
    if (pattern->kind == TY_LIST || pattern->kind == TY_OPTION)
        return match_type(pattern->elem, actual->elem, scheme, sub);
    if (pattern->kind == TY_FUN) {
        if (pattern->arity != actual->arity) return false;
        for (i = 0U; i < pattern->arity; i++)
            if (!match_type(pattern->params[i], actual->params[i], scheme, sub)) return false;
        return match_type(pattern->result, actual->result, scheme, sub);
    }
    return type_eq(pattern, actual);
}

static Type *substitute_type(Arena *a, Type *t, Type *scheme, Type **sub) {
    size_t i;
    Type *r;
    for (i = 0U; i < scheme->variable_count; i++) if (t == scheme->variables[i]) return sub[i];
    if (t->kind == TY_LIST || t->kind == TY_OPTION) {
        r = type_new(a, t->kind); r->elem = substitute_type(a, t->elem, scheme, sub); return r;
    }
    if (t->kind == TY_FUN) {
        Type **ps = (Type **)aalloc(a, t->arity * sizeof(*ps));
        for (i = 0U; i < t->arity; i++) ps[i] = substitute_type(a, t->params[i], scheme, sub);
        return type_fun(a, ps, t->arity, substitute_type(a, t->result, scheme, sub));
    }
    return t;
}

static Type *check_type_app(Arena *a, const SExpr *x, TBind *env, Error *e) {
    Type *scheme;
    Type **sub;
    size_t i;
    if (x->count < 3U) {
        (void)fail(e, NLISP_PARSE_ERROR, x->span, "type-app requires a function and explicit types"); return NULL;
    }
    scheme = check_expr(a, x->items[1], env, e);
    if (scheme == NULL) return NULL;
    if (scheme->kind != TY_FORALL || x->count - 2U != scheme->variable_count) {
        (void)fail(e, NLISP_TYPE_ERROR, x->span, "type-app requires a polymorphic function and matching type arity"); return NULL;
    }
    sub = (Type **)aalloc(a, scheme->variable_count * sizeof(*sub));
    for (i = 0U; i < scheme->variable_count; i++) {
        sub[i] = parse_type(a, x->items[i + 2U], e);
        if (sub[i] == NULL) return NULL;
    }
    return substitute_type(a, scheme->result, scheme, sub);
}

static Type *check_if(Arena *a, const SExpr *x, TBind *env, Error *e) {
    Type want = {.kind = TY_BOOL};
    Type *c, *yes, *no;
    if (x->count != 4U) { (void)fail(e, NLISP_PARSE_ERROR, x->span, "if requires three expressions"); return NULL; }
    c = check_expr(a, x->items[1], env, e);
    if (c == NULL || !require(c, &want, x->items[1]->span, e, "if condition")) return NULL;
    yes = check_expr(a, x->items[2], env, e); no = check_expr(a, x->items[3], env, e);
    if (yes == NULL || no == NULL || !require(no, yes, x->items[3]->span, e, "if branches")) return NULL;
    return yes;
}

static Type *check_lambda(Arena *a, const SExpr *x, TBind *env, Error *e) {
    Param *ps; size_t n, i; Type *ret, *body; Type **types; TBind *local = env;
    if (x->count != 4U) { (void)fail(e, NLISP_PARSE_ERROR, x->span, "invalid lambda"); return NULL; }
    if (!parse_params(a, x->items[1], &ps, &n, e)) return NULL;
    ((SExpr *)x)->checked_parameters = ps;
    ((SExpr *)x)->checked_arity = n;
    ret = parse_type(a, x->items[2], e); if (ret == NULL) return NULL;
    types = (Type **)aalloc(a, n * sizeof(*types));
    for (i = 0U; i < n; i++) { local = tbind(a, local, ps[i].name, ps[i].type); types[i] = ps[i].type; }
    body = check_expr(a, x->items[3], local, e);
    if (body == NULL || !require(body, ret, x->items[3]->span, e, "lambda return")) return NULL;
    return type_fun(a, types, n, ret);
}

static Type *check_let(Arena *a, const SExpr *x, TBind *env, Error *e) {
    const SExpr *bs; const char **names; Type **types; size_t i; TBind *local = env;
    if (x->count != 3U || x->items[1]->kind != SX_LIST) {
        (void)fail(e, NLISP_PARSE_ERROR, x->span, "invalid let"); return NULL;
    }
    bs = x->items[1];
    names = (const char **)aalloc(a, bs->count * sizeof(*names));
    types = (Type **)aalloc(a, bs->count * sizeof(*types));
    for (i = 0U; i < bs->count; i++) {
        const SExpr *b = bs->items[i]; Type *got;
        if (b->kind != SX_LIST || b->count != 2U || b->items[0]->kind != SX_LIST ||
            b->items[0]->count != 2U || b->items[0]->items[0]->kind != SX_ATOM) {
            (void)fail(e, NLISP_PARSE_ERROR, b->span, "let binding is ((name Type) value)"); return NULL;
        }
        names[i] = b->items[0]->items[0]->atom;
        types[i] = parse_type(a, b->items[0]->items[1], e);
        got = check_expr(a, b->items[1], env, e);
        if (types[i] == NULL || got == NULL || !require(got, types[i], b->span, e, "let binding")) return NULL;
    }
    for (i = 0U; i < bs->count; i++) local = tbind(a, local, names[i], types[i]);
    return check_expr(a, x->items[2], local, e);
}

static Type *check_match(Arena *a, const SExpr *x, TBind *env, Error *e) {
    Type *scrut, *t1, *t2; const SExpr *empty = NULL, *full = NULL; size_t i;
    if (x->count != 4U) { (void)fail(e, NLISP_PARSE_ERROR, x->span, "match requires two clauses"); return NULL; }
    scrut = check_expr(a, x->items[1], env, e); if (scrut == NULL) return NULL;
    for (i = 2U; i < 4U; i++) {
        const SExpr *c = x->items[i], *p;
        if (c->kind != SX_LIST || c->count != 2U || c->items[0]->kind != SX_LIST) {
            (void)fail(e, NLISP_PARSE_ERROR, c->span, "invalid match clause"); return NULL;
        }
        p = c->items[0];
        if (scrut->kind == TY_LIST && p->count == 1U && is_atom(p->items[0], "Nil")) empty = c;
        else if (scrut->kind == TY_LIST && p->count == 3U && is_atom(p->items[0], "Cons") &&
                 p->items[1]->kind == SX_ATOM && p->items[2]->kind == SX_ATOM) full = c;
        else if (scrut->kind == TY_OPTION && p->count == 1U && is_atom(p->items[0], "None")) empty = c;
        else if (scrut->kind == TY_OPTION && p->count == 2U && is_atom(p->items[0], "Some") &&
                 p->items[1]->kind == SX_ATOM) full = c;
        else { (void)fail(e, NLISP_PARSE_ERROR, p->span, "pattern does not match scrutinee type"); return NULL; }
    }
    if (empty == NULL || full == NULL) {
        (void)fail(e, NLISP_TYPE_ERROR, x->span, "match must be exhaustive without duplicate clauses"); return NULL;
    }
    t1 = check_expr(a, empty->items[1], env, e);
    if (scrut->kind == TY_LIST) {
        TBind *local = tbind(a, env, full->items[0]->items[2]->atom, scrut);
        local = tbind(a, local, full->items[0]->items[1]->atom, scrut->elem);
        t2 = check_expr(a, full->items[1], local, e);
    } else {
        TBind *local = tbind(a, env, full->items[0]->items[1]->atom, scrut->elem);
        t2 = check_expr(a, full->items[1], local, e);
    }
    if (t1 == NULL || t2 == NULL || !require(t2, t1, x->span, e, "match clauses")) return NULL;
    return t1;
}

static Type *check_call(Arena *a, const SExpr *x, TBind *env, Error *e) {
    Type *f = check_expr(a, x->items[0], env, e); size_t i;
    Type *scheme = NULL;
    Type **sub = NULL;
    if (f == NULL) return NULL;
    if (f->kind == TY_FORALL) {
        scheme = f; f = scheme->result;
        sub = (Type **)aalloc(a, scheme->variable_count * sizeof(*sub));
    }
    if (f->kind != TY_FUN) { (void)fail(e, NLISP_TYPE_ERROR, x->span, "attempted to call a non-function"); return NULL; }
    if (x->count - 1U != f->arity) {
        (void)fail(e, NLISP_TYPE_ERROR, x->span, "function expects %zu arguments, got %zu", f->arity, x->count - 1U);
        return NULL;
    }
    for (i = 0U; i < f->arity; i++) {
        Type *got = check_expr(a, x->items[i + 1U], env, e);
        if (got == NULL) return NULL;
        if (scheme != NULL) {
            if (!match_type(f->params[i], got, scheme, sub)) {
                (void)fail(e, NLISP_TYPE_ERROR, x->items[i + 1U]->span,
                           "inconsistent type argument constraints; use matching monomorphic arguments");
                return NULL;
            }
        } else if (!require(got, f->params[i], x->items[i + 1U]->span, e, "argument")) return NULL;
    }
    if (scheme != NULL) {
        for (i = 0U; i < scheme->variable_count; i++) if (sub[i] == NULL) {
            (void)fail(e, NLISP_TYPE_ERROR, x->span,
                       "cannot determine type argument '%s' from arguments; use type-app",
                       scheme->variables[i]->name); return NULL;
        }
        return substitute_type(a, f->result, scheme, sub);
    }
    return f->result;
}

static Type *check_expr(Arena *a, const SExpr *x, TBind *env, Error *e) {
    int64_t ignored;
    if (x->expanded != NULL) return check_expr(a, x->expanded, env, e);
    if (x->kind == SX_ATOM) {
        Type *t;
        if (strcmp(x->atom, "true") == 0 || strcmp(x->atom, "false") == 0) return type_new(a, TY_BOOL);
        if (strcmp(x->atom, "unit") == 0) return type_new(a, TY_UNIT);
        if (integer_atom(x->atom, &ignored)) return type_new(a, TY_INT);
        t = tlookup(x->origin == NULL ? env : x->origin->type_env, x->atom);
        if (t == NULL) (void)fail(e, NLISP_TYPE_ERROR, x->span, "unbound identifier '%s'", x->atom);
        return t;
    }
    if (x->count == 0U) { (void)fail(e, NLISP_PARSE_ERROR, x->span, "empty list is not an expression"); return NULL; }
    if (x->items[0]->kind == SX_ATOM) {
        Macro *m;
        for (m = a->macros; m != NULL; m = m->next)
            if (strcmp(m->name, x->items[0]->atom) == 0) {
                if (m->type_env == NULL ||
                    (x->items[0]->origin != NULL &&
                     m == x->items[0]->origin))
                    break;
                return check_macro_call(a, x, m, env, e);
            }
    }
    if (is_atom(x->items[0], "type-app")) return check_type_app(a, x, env, e);
    if (is_atom(x->items[0], "if")) return check_if(a, x, env, e);
    if (is_atom(x->items[0], "lambda")) return check_lambda(a, x, env, e);
    if (is_atom(x->items[0], "let")) return check_let(a, x, env, e);
    if (is_atom(x->items[0], "match")) return check_match(a, x, env, e);
    if (is_atom(x->items[0], "begin")) {
        Type *r = NULL; size_t i;
        if (x->count < 2U) { (void)fail(e, NLISP_PARSE_ERROR, x->span, "begin requires an expression"); return NULL; }
        for (i = 1U; i < x->count; i++) { r = check_expr(a, x->items[i], env, e); if (r == NULL) return NULL; }
        return r;
    }
    if (is_atom(x->items[0], "Nil") || is_atom(x->items[0], "None")) {
        Type *r;
        if (x->count != 2U) { (void)fail(e, NLISP_PARSE_ERROR, x->span, "constructor requires an explicit type"); return NULL; }
        r = type_new(a, is_atom(x->items[0], "Nil") ? TY_LIST : TY_OPTION);
        r->elem = parse_type(a, x->items[1], e); return r->elem == NULL ? NULL : r;
    }
    if (is_atom(x->items[0], "Some")) {
        Type *elem, *got, *r;
        if (x->count != 3U) { (void)fail(e, NLISP_PARSE_ERROR, x->span, "Some requires type and value"); return NULL; }
        elem = parse_type(a, x->items[1], e); got = check_expr(a, x->items[2], env, e);
        if (elem == NULL || got == NULL || !require(got, elem, x->span, e, "Some value")) return NULL;
        r = type_new(a, TY_OPTION); r->elem = elem; return r;
    }
    if (is_atom(x->items[0], "Cons")) {
        Type *elem, *head, *tail, *r;
        if (x->count != 4U) { (void)fail(e, NLISP_PARSE_ERROR, x->span, "Cons requires type, head, and tail"); return NULL; }
        elem = parse_type(a, x->items[1], e); head = check_expr(a, x->items[2], env, e);
        tail = check_expr(a, x->items[3], env, e);
        if (elem == NULL || head == NULL || tail == NULL || !require(head, elem, x->span, e, "Cons head")) return NULL;
        r = type_new(a, TY_LIST); r->elem = elem;
        if (!require(tail, r, x->span, e, "Cons tail")) return NULL;
        return r;
    }
    return check_call(a, x, env, e);
}

static TBind *add_builtin_type(Arena *a, TBind *env, const char *name, TypeKind result) {
    Type **ps = (Type **)aalloc(a, 2U * sizeof(*ps));
    ps[0] = type_new(a, TY_INT); ps[1] = type_new(a, TY_INT);
    return tbind(a, env, name, type_fun(a, ps, 2U, type_new(a, result)));
}

static TBind *type_builtins(Arena *a) {
    TBind *env = NULL;
    env = add_builtin_type(a, env, "+", TY_INT);
    env = add_builtin_type(a, env, "-", TY_INT);
    env = add_builtin_type(a, env, "*", TY_INT);
    env = add_builtin_type(a, env, "<=", TY_BOOL);
    env = add_builtin_type(a, env, "integer=", TY_BOOL);
    return env;
}

static bool check_program(Arena *a, Program *p, Error *e) {
    TBind *env = type_builtins(a); size_t i, j;
    Type integer = {.kind = TY_INT};
    for (i = 0U; i < p->count; i++) {
        const char *name = p->data[i].kind == D_FUN ? p->data[i].as.fun.name : p->data[i].as.val.name;
        Macro *m;
        for (m = a->macros; m != NULL; m = m->next)
            if (strcmp(name, m->name) == 0)
                return fail(e, NLISP_TYPE_ERROR, m->pattern->span,
                            "macro name conflicts with top-level value '%s'", name);
    }
    for (i = 0U; i < p->count; i++) if (p->data[i].kind == D_FUN) {
        FunDef *f = &p->data[i].as.fun;
        if (tlookup(env, f->name) != NULL) return fail(e, NLISP_TYPE_ERROR, f->span, "duplicate name '%s'", f->name);
        env = tbind(a, env, f->name, f->type);
    }
    for (i = 0U; i < p->count; i++) {
        if (!prepare_macros(a, a->macros, i, env, e)) return false;
        if (p->data[i].kind == D_FUN) {
            FunDef *f = &p->data[i].as.fun; TBind *local = env; Type *got;
            a->type_variables = f->type->kind == TY_FORALL ? f->type->variables : NULL;
            a->type_variable_count = f->type->kind == TY_FORALL ? f->type->variable_count : 0U;
            for (j = 0U; j < f->arity; j++) local = tbind(a, local, f->params[j].name, f->params[j].type);
            got = check_expr(a, f->body, local, e);
            a->type_variables = NULL; a->type_variable_count = 0U;
            if (got == NULL || !require(got, f->ret, f->body->span, e, "function return")) return false;
        } else {
            ValDef *v = &p->data[i].as.val; Type *got;
            if (tlookup(env, v->name) != NULL) return fail(e, NLISP_TYPE_ERROR, v->span, "duplicate name '%s'", v->name);
            got = check_expr(a, v->init, env, e);
            if (got == NULL || !require(got, v->type, v->init->span, e, "definition")) return false;
            env = tbind(a, env, v->name, v->type);
        }
    }
    if (!prepare_macros(a, a->macros, p->count, env, e)) return false;
    {
        Type *main_t = tlookup(env, "main");
        if (main_t == NULL || main_t->kind != TY_FUN || main_t->arity != 0U || !type_eq(main_t->result, &integer))
            return fail(e, NLISP_TYPE_ERROR, (Span){1U, 1U},
                        "program requires main of type (Function () Integer)");
    }
    return true;
}

typedef struct Value Value;
typedef struct RBind RBind;
typedef enum { BI_ADD, BI_SUB, BI_MUL, BI_LE, BI_EQ } Builtin;
typedef enum { V_BOOL, V_INT, V_UNIT, V_CLOSURE, V_BUILTIN, V_NIL, V_CONS, V_NONE, V_SOME } VKind;
typedef struct { Param *params; size_t arity; SExpr *body; RBind *env; } Closure;
struct Value {
    VKind kind;
    union {
        bool boolean; int64_t integer; Closure closure; Builtin builtin;
        struct { Value *head, *tail; } cons; Value *some;
    } as;
};
struct RBind { const char *name; Value *value; RBind *next; };
typedef struct { Arena *a; Error *e; } Runtime;

static Value *vnew(Runtime *r, VKind k) { Value *v = (Value *)aalloc(r->a, sizeof(*v)); v->kind = k; return v; }
static RBind *rbind(Runtime *r, RBind *env, const char *name, Value *v) {
    RBind *b = (RBind *)aalloc(r->a, sizeof(*b)); b->name = name; b->value = v; b->next = env; return b;
}
static Value *rlookup(RBind *env, const char *name) {
    for (; env != NULL; env = env->next) if (strcmp(env->name, name) == 0) return env->value;
    return NULL;
}

static bool add_ok(int64_t a, int64_t b, int64_t *r) {
    if ((b > 0 && a > INT64_MAX - b) || (b < 0 && a < INT64_MIN - b)) return false;
    *r = a + b; return true;
}
static bool sub_ok(int64_t a, int64_t b, int64_t *r) {
    if ((b < 0 && a > INT64_MAX + b) || (b > 0 && a < INT64_MIN + b)) return false;
    *r = a - b; return true;
}
static bool mul_ok(int64_t a, int64_t b, int64_t *r) {
    if (a == 0 || b == 0) { *r = 0; return true; }
    if ((a == -1 && b == INT64_MIN) || (b == -1 && a == INT64_MIN)) return false;
    if (a > 0) {
        if ((b > 0 && a > INT64_MAX / b) || (b < 0 && b < INT64_MIN / a)) return false;
    } else {
        if ((b > 0 && a < INT64_MIN / b) || (b < 0 && a < INT64_MAX / b)) return false;
    }
    *r = a * b; return true;
}

static Value *eval(Runtime *r, const SExpr *x, RBind *env);

static Value *apply(Runtime *r, Value *f, Value **args, size_t n, Span span) {
    size_t i; RBind *local; Value *v; int64_t result = 0;
    if (f->kind == V_BUILTIN) {
        if (n != 2U || args[0]->kind != V_INT || args[1]->kind != V_INT) {
            (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "internal builtin type error"); return NULL;
        }
        if (f->as.builtin == BI_LE || f->as.builtin == BI_EQ) {
            v = vnew(r, V_BOOL);
            v->as.boolean = f->as.builtin == BI_LE ? args[0]->as.integer <= args[1]->as.integer
                                                   : args[0]->as.integer == args[1]->as.integer;
            return v;
        }
        if ((f->as.builtin == BI_ADD && !add_ok(args[0]->as.integer, args[1]->as.integer, &result)) ||
            (f->as.builtin == BI_SUB && !sub_ok(args[0]->as.integer, args[1]->as.integer, &result)) ||
            (f->as.builtin == BI_MUL && !mul_ok(args[0]->as.integer, args[1]->as.integer, &result))) {
            (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "Integer overflow"); return NULL;
        }
        v = vnew(r, V_INT); v->as.integer = result; return v;
    }
    if (f->kind != V_CLOSURE || n != f->as.closure.arity) {
        (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "internal call error"); return NULL;
    }
    local = f->as.closure.env;
    for (i = 0U; i < n; i++) local = rbind(r, local, f->as.closure.params[i].name, args[i]);
    return eval(r, f->as.closure.body, local);
}

static Value *eval_match(Runtime *r, const SExpr *x, RBind *env) {
    Value *s = eval(r, x->items[1], env); size_t i;
    if (s == NULL) return NULL;
    for (i = 2U; i < 4U; i++) {
        const SExpr *c = x->items[i], *p = c->items[0];
        if (s->kind == V_NIL && is_atom(p->items[0], "Nil")) return eval(r, c->items[1], env);
        if (s->kind == V_CONS && is_atom(p->items[0], "Cons")) {
            RBind *local = rbind(r, env, p->items[2]->atom, s->as.cons.tail);
            local = rbind(r, local, p->items[1]->atom, s->as.cons.head);
            return eval(r, c->items[1], local);
        }
        if (s->kind == V_NONE && is_atom(p->items[0], "None")) return eval(r, c->items[1], env);
        if (s->kind == V_SOME && is_atom(p->items[0], "Some")) {
            RBind *local = rbind(r, env, p->items[1]->atom, s->as.some);
            return eval(r, c->items[1], local);
        }
    }
    (void)fail(r->e, NLISP_RUNTIME_ERROR, x->span, "internal match error"); return NULL;
}

static Value *eval(Runtime *r, const SExpr *x, RBind *env) {
    int64_t number;
    if (x->expanded != NULL) return eval(r, x->expanded, env);
    if (x->kind == SX_ATOM) {
        Value *v;
        if (strcmp(x->atom, "true") == 0 || strcmp(x->atom, "false") == 0) {
            v = vnew(r, V_BOOL); v->as.boolean = strcmp(x->atom, "true") == 0; return v;
        }
        if (strcmp(x->atom, "unit") == 0) return vnew(r, V_UNIT);
        if (integer_atom(x->atom, &number)) { v = vnew(r, V_INT); v->as.integer = number; return v; }
        v = rlookup(x->origin == NULL ? env : x->origin->runtime_env, x->atom);
        if (v == NULL) (void)fail(r->e, NLISP_RUNTIME_ERROR, x->span, "internal unbound name");
        return v;
    }
    if (is_atom(x->items[0], "if")) {
        Value *c = eval(r, x->items[1], env); if (c == NULL) return NULL;
        return eval(r, x->items[c->as.boolean ? 2U : 3U], env);
    }
    if (is_atom(x->items[0], "begin")) {
        Value *v = NULL; size_t i;
        for (i = 1U; i < x->count; i++) { v = eval(r, x->items[i], env); if (v == NULL) return NULL; }
        return v;
    }
    if (is_atom(x->items[0], "let")) {
        const SExpr *bs = x->items[1]; Value **vs; RBind *local = env; size_t i;
        vs = (Value **)aalloc(r->a, bs->count * sizeof(*vs));
        for (i = 0U; i < bs->count; i++) { vs[i] = eval(r, bs->items[i]->items[1], env); if (vs[i] == NULL) return NULL; }
        for (i = 0U; i < bs->count; i++) local = rbind(r, local, bs->items[i]->items[0]->items[0]->atom, vs[i]);
        return eval(r, x->items[2], local);
    }
    if (is_atom(x->items[0], "lambda")) {
        Param *ps = (Param *)x->checked_parameters; size_t n = x->checked_arity; Value *v;
        v = vnew(r, V_CLOSURE); v->as.closure = (Closure){ps, n, x->items[3], env}; return v;
    }
    if (is_atom(x->items[0], "type-app")) return eval(r, x->items[1], env);
    if (is_atom(x->items[0], "match")) return eval_match(r, x, env);
    if (is_atom(x->items[0], "Nil")) return vnew(r, V_NIL);
    if (is_atom(x->items[0], "None")) return vnew(r, V_NONE);
    if (is_atom(x->items[0], "Some")) {
        Value *item = eval(r, x->items[2], env), *v; if (item == NULL) return NULL;
        v = vnew(r, V_SOME); v->as.some = item; return v;
    }
    if (is_atom(x->items[0], "Cons")) {
        Value *head = eval(r, x->items[2], env), *tail, *v; if (head == NULL) return NULL;
        tail = eval(r, x->items[3], env); if (tail == NULL) return NULL;
        v = vnew(r, V_CONS); v->as.cons.head = head; v->as.cons.tail = tail; return v;
    }
    {
        Value *f = eval(r, x->items[0], env); Value **args; size_t n = x->count - 1U, i;
        if (f == NULL) return NULL;
        args = (Value **)aalloc(r->a, n * sizeof(*args));
        for (i = 0U; i < n; i++) { args[i] = eval(r, x->items[i + 1U], env); if (args[i] == NULL) return NULL; }
        return apply(r, f, args, n, x->span);
    }
}

static RBind *bind_builtin(Runtime *r, RBind *env, const char *name, Builtin bi) {
    Value *v = vnew(r, V_BUILTIN); v->as.builtin = bi; return rbind(r, env, name, v);
}

static RBind *runtime_builtins(Runtime *r) {
    RBind *env = NULL;
    env = bind_builtin(r, env, "+", BI_ADD); env = bind_builtin(r, env, "-", BI_SUB);
    env = bind_builtin(r, env, "*", BI_MUL); env = bind_builtin(r, env, "<=", BI_LE);
    env = bind_builtin(r, env, "integer=", BI_EQ); return env;
}

static Value *run_program(Arena *a, Program *p, Error *e) {
    Runtime r = {a, e}; RBind *env = runtime_builtins(&r);
    Value **closures = (Value **)aalloc(a, p->count * sizeof(*closures));
    size_t count = 0U, i, j; Value *main_value;
    for (i = 0U; i < p->count; i++) if (p->data[i].kind == D_FUN) {
        FunDef *f = &p->data[i].as.fun; Value *v = vnew(&r, V_CLOSURE);
        v->as.closure = (Closure){f->params, f->arity, f->body, NULL};
        closures[count++] = v; env = rbind(&r, env, f->name, v);
    }
    for (i = 0U; i < count; i++) closures[i]->as.closure.env = env;
    for (i = 0U; i < p->count; i++) if (p->data[i].kind == D_VAL) {
        Value *v;
        Macro *m;
        for (m = a->macros; m != NULL; m = m->next)
            if (m->declaration_index <= i && m->runtime_env == NULL) m->runtime_env = env;
        for (j = 0U; j < count; j++) closures[j]->as.closure.env = env;
        v = eval(&r, p->data[i].as.val.init, env); if (v == NULL) return NULL;
        env = rbind(&r, env, p->data[i].as.val.name, v);
    }
    {
        Macro *m;
        for (m = a->macros; m != NULL; m = m->next)
            if (m->runtime_env == NULL) m->runtime_env = env;
    }
    for (i = 0U; i < count; i++) closures[i]->as.closure.env = env;
    main_value = rlookup(env, "main");
    return apply(&r, main_value, NULL, 0U, (Span){1U, 1U});
}

static void print_value(FILE *out, const Value *v) {
    switch (v->kind) {
        case V_BOOL: fputs(v->as.boolean ? "true" : "false", out); break;
        case V_INT: (void)fprintf(out, "%lld", (long long)v->as.integer); break;
        case V_UNIT: fputs("unit", out); break;
        case V_CLOSURE: case V_BUILTIN: fputs("<function>", out); break;
        case V_NIL: fputs("(Nil)", out); break;
        case V_CONS:
            fputs("(Cons ", out); print_value(out, v->as.cons.head); fputc(' ', out);
            print_value(out, v->as.cons.tail); fputc(')', out); break;
        case V_NONE: fputs("(None)", out); break;
        case V_SOME: fputs("(Some ", out); print_value(out, v->as.some); fputc(')', out); break;
    }
}

static char *read_source(const char *path, size_t *len, Error *e) {
    FILE *f = fopen(path, "rb"); long size; char *buf; size_t got;
    if (f == NULL) { (void)fail(e, NLISP_IO_ERROR, (Span){0U, 0U}, "cannot open file"); return NULL; }
    if (fseek(f, 0L, SEEK_END) != 0 || (size = ftell(f)) < 0L || fseek(f, 0L, SEEK_SET) != 0) {
        fclose(f); (void)fail(e, NLISP_IO_ERROR, (Span){0U, 0U}, "cannot determine file size"); return NULL;
    }
    buf = (char *)malloc((size_t)size + 1U);
    if (buf == NULL) { fclose(f); fputs("nlisp: out of memory\n", stderr); abort(); }
    got = fread(buf, 1U, (size_t)size, f);
    if (got != (size_t)size || fclose(f) != 0) {
        free(buf); (void)fail(e, NLISP_IO_ERROR, (Span){0U, 0U}, "cannot read file"); return NULL;
    }
    buf[got] = '\0'; *len = got; return buf;
}

static void report(FILE *stream, const char *path, const Error *e) {
    if (e->span.line == 0U) (void)fprintf(stream, "%s: %s\n", path, e->message);
    else (void)fprintf(stream, "%s:%zu:%zu: %s\n", path, e->span.line, e->span.column, e->message);
}

static void print_expansion(FILE *out, const SExpr *x) {
    size_t i;
    if (x->expanded != NULL) { print_expansion(out, x->expanded); return; }
    if (x->kind == SX_ATOM) { fputs(x->atom, out); return; }
    fputc('(', out);
    for (i = 0U; i < x->count; i++) {
        if (i != 0U) fputc(' ', out);
        print_expansion(out, x->items[i]);
    }
    fputc(')', out);
}

static NLispStatus process(const char *path, int mode, FILE *out, FILE *err) {
    Arena a = {0}; Error e = {false, NLISP_OK, {0U, 0U}, {0}};
    char *source; size_t len = 0U; Tokens ts = {NULL, 0U}; Forms forms = {NULL, 0U};
    Program p = {NULL, 0U}; Value *result = NULL;
    source = read_source(path, &len, &e);
    if (source != NULL && lex(&a, source, len, &ts, &e) && parse_forms(&a, ts, &forms, &e) &&
        collect_macros(&a, &forms, &e) &&
        parse_program(&a, forms, &p, &e) && check_program(&a, &p, &e) &&
        check_program(&a, &p, &e)) {
        if (mode == 1) {
            result = run_program(&a, &p, &e);
            if (result != NULL) { print_value(out, result); fputc('\n', out); }
        } else if (mode == 2) {
            size_t i;
            for (i = 0U; i < forms.count; i++) {
                print_expansion(out, forms.data[i]); fputc('\n', out);
            }
        } else fputs("ok\n", out);
    }
    free(source);
    if (e.set) { report(err, path, &e); adestroy(&a); return e.status; }
    adestroy(&a); return NLISP_OK;
}

NLispStatus nlisp_check_file(const char *path, FILE *out, FILE *err) {
    return process(path, 0, out, err);
}
NLispStatus nlisp_run_file(const char *path, FILE *out, FILE *err) {
    return process(path, 1, out, err);
}

NLispStatus nlisp_expand_file(const char *path, FILE *out, FILE *err) {
    return process(path, 2, out, err);
}
