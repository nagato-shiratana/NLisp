#include "nlisp.h"

#include <ctype.h>
#include <fenv.h>
#include <float.h>
#include <limits.h>
#include <math.h>
#include <gmp.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

_Static_assert(CHAR_BIT == 8 && FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024 &&
               sizeof(double) == 8U, "NLisp requires IEEE 754 binary64 double");

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

typedef struct Allocation { void *ptr; void (*cleanup)(void *); struct Allocation *next; } Allocation;
struct Type;
struct Macro;
struct MacroTrace;
struct SExpr;
struct IdentityKey;
struct NameObservation;
typedef struct {
    Allocation *head;
    struct Type **type_variables;
    size_t type_variable_count;
    struct Macro *macros;
    size_t fresh_scope;
    size_t check_index;
    bool checking_templates;
    NLispLimits limits;
    bool capture_trace;
    struct SExpr **source_forms, **normalized_forms;
    size_t source_count, normalized_count;
    struct MacroTrace *trace_head, *trace_tail;
    size_t trace_count;
    struct IdentityKey *identity_keys[1024];
    size_t type_identity_count;
    struct NameObservation *name_head, *name_tail;
    size_t name_nodes;
    size_t expansions, generated_nodes, copy_depth, check_depth, check_steps;
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
    x->ptr = p; x->cleanup = NULL; x->next = a->head; a->head = x;
    return p;
}

static char *astr(Arena *a, const char *s, size_t n) {
    char *r = (char *)aalloc(a, n + 1U);
    if (n != 0U) memcpy(r, s, n);
    r[n] = '\0';
    return r;
}

typedef struct IdentityKey {
    const void *key;
    size_t identity;
    struct IdentityKey *next;
} IdentityKey;

static IdentityKey *identity_key(Arena *a, const void *key) {
    IdentityKey *entry;
    size_t bucket = ((uintptr_t)key >> 3U) % 1024U;
    for (entry = a->identity_keys[bucket]; entry != NULL; entry = entry->next)
        if (entry->key == key) return entry;
    return NULL;
}

static void register_identity(Arena *a, const void *key, size_t identity) {
    size_t bucket = ((uintptr_t)key >> 3U) % 1024U;
    IdentityKey *entry;
    if (identity_key(a, key) != NULL) return;
    entry = (IdentityKey *)aalloc(a, sizeof(*entry));
    entry->key = key; entry->identity = identity;
    entry->next = a->identity_keys[bucket]; a->identity_keys[bucket] = entry;
}

static size_t name_identity(Arena *a, const char *name) {
    IdentityKey *entry = identity_key(a, name);
    size_t scope;
    if (entry != NULL) return entry->identity;
    if (strncmp(name, "#%nlisp", 7U) == 0 && sscanf(name + 7U, "%zu", &scope) == 1 &&
        scope <= (SIZE_MAX - 2U) / 3U) {
        size_t identity = scope * 3U + 2U;
        register_identity(a, name, identity); return identity;
    }
    return SIZE_MAX;
}

static size_t type_identity(Arena *a, const void *type) {
    IdentityKey *entry = identity_key(a, type);
    if (entry != NULL) return entry->identity;
    register_identity(a, type, a->type_identity_count++);
    return identity_key(a, type)->identity;
}

static void adestroy(Arena *a) {
    Allocation *x = a->head;
    while (x != NULL) {
        Allocation *next = x->next;
        if (x->cleanup != NULL) x->cleanup(x->ptr);
        free(x->ptr); free(x); x = next;
    }
    a->head = NULL;
}

typedef enum { TK_LEFT, TK_RIGHT, TK_ATOM, TK_END } TokenKind;
typedef struct { TokenKind kind; Span span; char *text; } Token;
typedef struct { Token *data; size_t count; } Tokens;

typedef struct { char *data; size_t length; } Text;

static bool scalar(uint32_t c) {
    return c <= 0x10ffffU && !(c >= 0xd800U && c <= 0xdfffU);
}

static bool utf8_next(const char *s, size_t length, size_t *pos, uint32_t *out) {
    unsigned char first;
    uint32_t value, minimum;
    size_t count, i;
    if (*pos >= length) return false;
    first = (unsigned char)s[(*pos)++];
    if (first < 0x80U) { *out = first; return true; }
    if (first >= 0xc2U && first <= 0xdfU) { count = 1U; value = first & 31U; minimum = 0x80U; }
    else if (first >= 0xe0U && first <= 0xefU) { count = 2U; value = first & 15U; minimum = 0x800U; }
    else if (first >= 0xf0U && first <= 0xf4U) { count = 3U; value = first & 7U; minimum = 0x10000U; }
    else return false;
    for (i = 0U; i < count; i++) {
        unsigned char next;
        if (*pos >= length) return false;
        next = (unsigned char)s[(*pos)++];
        if ((next & 0xc0U) != 0x80U) return false;
        value = (value << 6) | (next & 63U);
    }
    if (value < minimum || !scalar(value)) return false;
    *out = value; return true;
}

static void utf8_put(char *out, size_t *length, uint32_t c) {
    if (c < 0x80U) out[(*length)++] = (char)c;
    else if (c < 0x800U) {
        out[(*length)++] = (char)(0xc0U | (c >> 6));
        out[(*length)++] = (char)(0x80U | (c & 63U));
    } else if (c < 0x10000U) {
        out[(*length)++] = (char)(0xe0U | (c >> 12));
        out[(*length)++] = (char)(0x80U | ((c >> 6) & 63U));
        out[(*length)++] = (char)(0x80U | (c & 63U));
    } else {
        out[(*length)++] = (char)(0xf0U | (c >> 18));
        out[(*length)++] = (char)(0x80U | ((c >> 12) & 63U));
        out[(*length)++] = (char)(0x80U | ((c >> 6) & 63U));
        out[(*length)++] = (char)(0x80U | (c & 63U));
    }
}

static bool unicode_escape(const char *s, size_t *pos, uint32_t *out) {
    size_t digits = 0U;
    uint32_t c = 0U;
    if (s[(*pos)++] != 'u' || s[(*pos)++] != '{') return false;
    while (s[*pos] != '}' && s[*pos] != '\0') {
        unsigned char h = (unsigned char)s[(*pos)++];
        unsigned int v;
        if (h >= '0' && h <= '9') v = h - '0';
        else if (h >= 'a' && h <= 'f') v = h - 'a' + 10U;
        else if (h >= 'A' && h <= 'F') v = h - 'A' + 10U;
        else return false;
        if (++digits > 6U) return false;
        c = c * 16U + v;
    }
    if (digits == 0U || s[*pos] != '}' || !scalar(c)) return false;
    (*pos)++; *out = c; return true;
}

static bool string_literal(Arena *a, const char *s, Text *out) {
    size_t i = 1U, length = strlen(s), used = 0U;
    char *decoded;
    if (length < 2U || s[0] != '"' || s[length - 1U] != '"') return false;
    decoded = (char *)aalloc(a, length + 1U);
    while (i < length - 1U) {
        uint32_t c;
        if (s[i] == '\\') {
            i++;
            switch (s[i]) {
                case 'n': c = '\n'; i++; break;
                case 'r': c = '\r'; i++; break;
                case 't': c = '\t'; i++; break;
                case '"': c = '"'; i++; break;
                case '\\': c = '\\'; i++; break;
                case 'u': if (!unicode_escape(s, &i, &c)) return false; break;
                default: return false;
            }
        } else if (!utf8_next(s, length - 1U, &i, &c) || c == '"') return false;
        if (i > length - 1U) return false;
        utf8_put(decoded, &used, c);
    }
    decoded[used] = '\0'; out->data = decoded; out->length = used; return true;
}

static bool character_literal(const char *s, uint32_t *out) {
    size_t i = 2U, length = strlen(s);
    if (length < 3U || s[0] != '#' || s[1] != '\\') return false;
    if (strcmp(s + 2U, "newline") == 0) { *out = '\n'; return true; }
    if (strcmp(s + 2U, "space") == 0) { *out = ' '; return true; }
    if (strcmp(s + 2U, "tab") == 0) { *out = '\t'; return true; }
    if (s[2] == 'u' && s[3] == '{') return unicode_escape(s, &i, out) && i == length;
    return utf8_next(s, length, &i, out) && i == length;
}

/* Unicode 18.0 White_Space (PropList.txt), as required by SPECIFICATION 4.1. */
static bool unicode_space(uint32_t c) {
    return (c >= 0x9U && c <= 0xdU) || c == 0x20U || c == 0x85U || c == 0xa0U ||
           c == 0x1680U || (c >= 0x2000U && c <= 0x200aU) || c == 0x2028U ||
           c == 0x2029U || c == 0x202fU || c == 0x205fU || c == 0x3000U;
}

static bool line_end(uint32_t c) {
    return c == '\r' || c == '\n' || c == 0x85U || c == 0x2028U || c == 0x2029U;
}

static bool delimiter_at(const char *source, size_t length, size_t position) {
    uint32_t c;
    if (!utf8_next(source, length, &position, &c)) return true;
    return c == '(' || c == ')' || c == ';' || c == '"' || unicode_space(c);
}

static void advance_scalar(const char *source, size_t length, size_t *position, size_t *column) {
    uint32_t ignored;
    (void)utf8_next(source, length, position, &ignored);
    (*column)++;
}

static bool lex(Arena *a, const char *src, size_t len, Tokens *out, Error *e) {
    size_t i = 0U, line = 1U, col = 1U, count = 0U;
    Token *ts = (Token *)aalloc(a, (len + 1U) * sizeof(*ts));
    {
        size_t p = 0U; uint32_t c;
        while (p < len) if (!utf8_next(src, len, &p, &c) || c == 0U)
            return fail(e, NLISP_PARSE_ERROR, (Span){1U, p}, "invalid UTF-8 or NUL in source");
    }
    while (i < len) {
        char c = src[i];
        size_t next_position = i;
        uint32_t codepoint;
        (void)utf8_next(src, len, &next_position, &codepoint);
        if (c == '\r' || c == '\n') {
            if (c == '\r' && i + 1U < len && src[i + 1U] == '\n') i++;
            i++; line++; col = 1U; continue;
        }
        if (unicode_space(codepoint)) {
            i = next_position;
            if (line_end(codepoint)) { line++; col = 1U; } else col++;
            continue;
        }
        if (c == ';') {
            while (i < len) {
                size_t after = i;
                uint32_t comment;
                (void)utf8_next(src, len, &after, &comment);
                if (line_end(comment)) break;
                i = after; col++;
            }
            continue;
        }
        if (c == '(' || c == ')') {
            ts[count++] = (Token){c == '(' ? TK_LEFT : TK_RIGHT, {line, col}, NULL};
            i++; col++; continue;
        }
        if (c == '"') {
            size_t start = i, start_col = col, start_line = line;
            bool closed = false;
            Text ignored;
            i++; col++;
            while (i < len) {
                char next = src[i++]; col++;
                if (next == '"') { closed = true; break; }
                if (next == '\\' && i < len) { i++; col++; }
                else if (next == '\n') { line++; col = 1U; }
            }
            ts[count] = (Token){TK_ATOM, {start_line, start_col}, astr(a, src + start, i - start)};
            if (!closed || !string_literal(a, ts[count].text, &ignored))
                return fail(e, NLISP_PARSE_ERROR, ts[count].span, "invalid string literal or escape");
            count++; continue;
        }
        if (c == '#' && i + 1U < len && src[i + 1U] == '\\') {
            size_t start = i, start_col = col;
            uint32_t ignored;
            i += 2U; col += 2U;
            if (i < len && (src[i] == '(' || src[i] == ')' || src[i] == ';' || src[i] == '"')) { i++; col++; }
            else while (i < len && !delimiter_at(src, len, i)) advance_scalar(src, len, &i, &col);
            ts[count] = (Token){TK_ATOM, {line, start_col}, astr(a, src + start, i - start)};
            if (!character_literal(ts[count].text, &ignored))
                return fail(e, NLISP_PARSE_ERROR, ts[count].span, "invalid character literal");
            count++; continue;
        }
        {
            size_t start = i, start_col = col;
            while (i < len && !delimiter_at(src, len, i)) advance_scalar(src, len, &i, &col);
            if (i - start >= 7U && strncmp(src + start, "#%nlisp", 7U) == 0)
                return fail(e, NLISP_PARSE_ERROR, (Span){line, start_col}, "reserved generated identifier prefix");
            ts[count++] = (Token){TK_ATOM, {line, start_col}, astr(a, src + start, i - start)};
        }
    }
    ts[count++] = (Token){TK_END, {line, col}, NULL};
    {
        size_t token;
        for (token = 0U; token < count; token++) if (ts[token].kind == TK_ATOM) {
            if (token > (SIZE_MAX - 4U) / 3U)
                return fail(e, NLISP_UNKNOWN, ts[token].span, "Unknown: binding identity range exhausted");
            register_identity(a, ts[token].text, 3U * (token + 1U) + 1U);
        }
    }
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
    size_t token_identity, resolved_identity;
    size_t logical_size;
    size_t logical_height;
    size_t raw_size, raw_height;
} SExpr;
typedef struct SNode { SExpr *value; struct SNode *next; } SNode;
typedef struct { Arena *a; Tokens ts; size_t pos; Error *e; size_t depth; } Parser;

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

static SExpr *parse_expr_inner(Parser *p);

static SExpr *parse_expr(Parser *p) {
    SExpr *result;
    if (p->depth >= p->a->limits.max_expansion_depth) {
        (void)fail(p->e, NLISP_UNKNOWN, p->ts.data[p->pos].span,
                   "Unknown: source syntax depth limit (%zu) exceeded", p->a->limits.max_expansion_depth);
        return NULL;
    }
    p->depth++; result = parse_expr_inner(p); p->depth--; return result;
}

static SExpr *parse_expr_inner(Parser *p) {
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
    r->kind = SX_ATOM; r->span = t.span; r->atom = t.text; r->token_identity = name_identity(p->a, t.text);
    return r;
}

typedef struct { SExpr **data; size_t count; } Forms;

static bool remember_forms(Arena *a, Forms forms, bool normalized) {
    SExpr **saved;
    if (!a->capture_trace) return true;
    saved = (SExpr **)aalloc(a, forms.count * sizeof(*saved));
    if (forms.count != 0U) memcpy(saved, forms.data, forms.count * sizeof(*saved));
    if (normalized) { a->normalized_forms = saved; a->normalized_count = forms.count; }
    else { a->source_forms = saved; a->source_count = forms.count; }
    return true;
}


static bool is_atom(const SExpr *x, const char *s);

/* Desugar a recursive group before assigning declaration indices. Every
   later phase, including scoped JSON export, sees the same flat ordering. */
static bool flatten_defrec(Arena *a, Forms *forms, Error *e) {
    size_t i, j, count = 0U, used = 0U;
    SExpr **data;
    for (i = 0U; i < forms->count; i++) {
        SExpr *form = forms->data[i];
        if (form->kind == SX_LIST && form->count > 0U && is_atom(form->items[0], "defrec")) {
            if (form->count != 2U || form->items[1]->kind != SX_LIST || form->items[1]->count == 0U)
                return fail(e, NLISP_PARSE_ERROR, form->span, "defrec requires a nonempty function group");
            count += form->items[1]->count;
        } else count++;
    }
    data = (SExpr **)aalloc(a, count * sizeof(*data));
    for (i = 0U; i < forms->count; i++) {
        SExpr *form = forms->data[i];
        if (form->kind != SX_LIST || form->count == 0U || !is_atom(form->items[0], "defrec")) {
            data[used++] = form; continue;
        }
        for (j = 0U; j < form->items[1]->count; j++) {
            SExpr *entry = form->items[1]->items[j], *decl, *keyword;
            size_t k;
            if (entry->kind != SX_LIST || (entry->count != 3U && entry->count != 4U) ||
                entry->items[0]->kind != SX_ATOM)
                return fail(e, NLISP_PARSE_ERROR, entry->span, "defrec member must be a function declaration without defun");
            decl = (SExpr *)aalloc(a, sizeof(*decl));
            keyword = (SExpr *)aalloc(a, sizeof(*keyword));
            keyword->kind = SX_ATOM; keyword->span = entry->span; keyword->atom = astr(a, "defun", 5U);
            decl->kind = SX_LIST; decl->span = entry->span; decl->count = entry->count + 1U;
            decl->items = (SExpr **)aalloc(a, decl->count * sizeof(*decl->items));
            decl->items[0] = keyword;
            for (k = 0U; k < entry->count; k++) decl->items[k + 1U] = entry->items[k];
            data[used++] = decl;
        }
    }
    forms->data = data; forms->count = used; return true;
}

static bool parse_forms(Arena *a, Tokens ts, Forms *out, Error *e) {
    Parser p = {a, ts, 0U, e, 0U};
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

static bool integer_atom(const char *s);
static bool float_atom(const char *s, double *out);

static bool identifier(const SExpr *x) {
    static const char *const reserved[] = {
        "true", "false", "unit", "define", "defun", "defrec", "lambda", "if", "let", "begin",
        "forall", "type-app", "match", "define-macro", "syntax-rules/typed",
        "Boolean", "Integer", "Float", "String", "Character", "Unit", "List", "Option", "Function", "Syntax",
        "Nil", "Cons", "None", "Some"
    };
    size_t i;
    double ignored;
    if (x->kind != SX_ATOM || x->atom[0] == '\0' || x->atom[0] == '"' ||
        (x->atom[0] == '#' && x->atom[1] == '\\') || integer_atom(x->atom) || float_atom(x->atom, &ignored))
        return false;
    for (i = 0U; i < sizeof(reserved) / sizeof(reserved[0]); i++)
        if (strcmp(x->atom, reserved[i]) == 0) return false;
    return true;
}

typedef enum { TY_BOOL, TY_INT, TY_UNIT, TY_FLOAT, TY_STRING, TY_CHAR, TY_FUN, TY_LIST, TY_OPTION, TY_VAR, TY_FORALL } TypeKind;
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
        if (strcmp(x->atom, "Float") == 0) return type_new(a, TY_FLOAT);
        if (strcmp(x->atom, "String") == 0) return type_new(a, TY_STRING);
        if (strcmp(x->atom, "Character") == 0) return type_new(a, TY_CHAR);
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
        case TY_BOOL: case TY_INT: case TY_UNIT: case TY_FLOAT: case TY_STRING: case TY_CHAR: return true;
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
        case TY_FLOAT: name = "Float"; break;
        case TY_STRING: name = "String"; break;
        case TY_CHAR: name = "Character"; break;
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
/* `Program.data` has one index space for the original, mixed source order.
   Runtime value slots are indexed by that same declaration index; GlobalIR's
   store instead uses a dense ordinal over only D_VAL entries. */
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
        if (!identifier(p->items[0]))
            return fail(e, NLISP_PARSE_ERROR, p->items[0]->span, "invalid parameter identifier");
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
            if (!identifier(f->items[1]))
                return fail(e, NLISP_PARSE_ERROR, f->items[1]->span, "invalid function identifier");
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
                    if (!identifier(q))
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
            if (!identifier(f->items[1]->items[0]))
                return fail(e, NLISP_PARSE_ERROR, f->items[1]->items[0]->span, "invalid value identifier");
            ds[i].kind = D_VAL; d = &ds[i].as.val; b = f->items[1];
            d->name = b->items[0]->atom; d->span = b->items[0]->span;
            d->type = parse_type(a, b->items[1], e); if (d->type == NULL) return false;
            d->init = f->items[2];
        } else return fail(e, NLISP_PARSE_ERROR, f->items[0]->span,
                           "unknown top-level declaration '%s'", f->items[0]->atom);
    }
    out->data = ds; out->count = forms.count; return true;
}

typedef struct TBind { const char *name; Type *type; size_t value_index, identity, type_tag; struct TBind *next; } TBind;
static TBind *tfind(TBind *env, const char *name) {
    for (; env != NULL; env = env->next) if (strcmp(env->name, name) == 0) return env;
    return NULL;
}
static Type *tlookup(TBind *env, const char *name) {
    TBind *binding = tfind(env, name); return binding == NULL ? NULL : binding->type;
}
static TBind *tbind(Arena *a, TBind *env, const char *name, Type *type) {
    TBind *b = (TBind *)aalloc(a, sizeof(*b)); b->name = name; b->type = type; b->value_index = SIZE_MAX; b->identity = name_identity(a, name); b->type_tag = type_identity(a, type); b->next = env; return b;
}

typedef struct NameObservation {
    const char *name;
    TBind *environment, *selected;
    size_t line, column, definition_index;
    struct NameObservation *next;
} NameObservation;

static bool observe_name(Arena *a, const char *name, TBind *environment, TBind *selected,
                         Span span, size_t definition_index, Error *e) {
    TBind *binding;
    size_t cost = 1U;
    NameObservation *observation;
    if (!a->capture_trace || a->checking_templates) return true;
    for (binding = environment; binding != NULL; binding = binding->next) {
        if (binding->identity == SIZE_MAX)
            return fail(e, NLISP_TYPE_ERROR, span, "unregistered lexical binding identity");
        if (cost >= a->limits.max_generated_nodes)
            return fail(e, NLISP_UNKNOWN, span, "Unknown: name correspondence evidence node limit exceeded");
        cost++;
    }
    if (cost > a->limits.max_generated_nodes - a->name_nodes)
        return fail(e, NLISP_UNKNOWN, span, "Unknown: name correspondence evidence node limit exceeded");
    a->name_nodes += cost;
    observation = (NameObservation *)aalloc(a, sizeof(*observation));
    observation->name = name; observation->environment = environment; observation->selected = selected;
    observation->line = span.line; observation->column = span.column;
    observation->definition_index = definition_index;
    if (a->name_tail != NULL) a->name_tail->next = observation; else a->name_head = observation;
    a->name_tail = observation; return true;
}

struct RBind;
typedef struct Macro {
    const char *name;
    SExpr *pattern, *contracts, *template_expr, *rule;
    Type **inputs, *output;
    size_t arity, declaration_index;
    TBind *type_env;
    struct RBind *runtime_env;
    struct Macro *next, *group;
} Macro;

typedef struct MacroTrace {
    Macro *definition;
    const SExpr *input;
    SExpr *substitution;
    size_t call_id, fresh_start, fresh_end;
    struct MacroTrace *next;
} MacroTrace;


/* Each record represents one arity rule; group identifies its declaration.
   Recursive rules are checked symbolically and expanded under a budget. */
static bool collect_macros(Arena *a, Forms *forms, Error *e) {
    size_t i, count = 0U;
    for (i = 0U; i < forms->count; i++) {
        SExpr *form = forms->data[i];
        if (form->kind == SX_LIST && form->count > 0U &&
            is_atom(form->items[0], "define-macro")) {
            SExpr *rules, *rule, *pattern, *contracts, *output;
            Macro *m, *previous;
            size_t j, k, rule_index;
            Macro *group = NULL;
            if (form->count != 3U || form->items[1]->kind != SX_ATOM ||
                form->items[2]->kind != SX_LIST)
                return fail(e, NLISP_PARSE_ERROR, form->span, "invalid define-macro");
            if (!identifier(form->items[1]))
                return fail(e, NLISP_PARSE_ERROR, form->items[1]->span, "invalid macro identifier");
            rules = form->items[2];
            if (rules->count < 2U || !is_atom(rules->items[0], "syntax-rules/typed"))
                return fail(e, NLISP_PARSE_ERROR, rules->span,
                            "syntax-rules/typed requires at least one rule");
            for (previous = a->macros; previous != NULL; previous = previous->next)
                if (strcmp(previous->name, form->items[1]->atom) == 0)
                    return fail(e, NLISP_TYPE_ERROR, form->span, "duplicate macro name");
            for (rule_index = 1U; rule_index < rules->count; rule_index++) {
                rule = rules->items[rule_index];
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
                    if (previous->group == group && previous->arity == contracts->count)
                        return fail(e, NLISP_TYPE_ERROR, rule->span, "duplicate macro rule arity");
                m = (Macro *)aalloc(a, sizeof(*m));
                m->name = form->items[1]->atom; m->pattern = pattern; m->contracts = contracts;
                m->rule = rule; m->template_expr = rule->items[3]; m->arity = contracts->count;
                m->declaration_index = count;
                if (group == NULL) group = m;
                m->group = group;
                m->inputs = (Type **)aalloc(a, m->arity * sizeof(*m->inputs));
                for (j = 0U; j < m->arity; j++) {
                    SExpr *c = contracts->items[j];
                    if (pattern->items[j + 1U]->kind != SX_ATOM ||
                        c->kind != SX_LIST || c->count != 2U ||
                        !is_atom(c->items[0], pattern->items[j + 1U]->atom) ||
                        c->items[1]->kind != SX_LIST || c->items[1]->count != 2U ||
                        !is_atom(c->items[1]->items[0], "Syntax"))
                        return fail(e, NLISP_PARSE_ERROR, c->span, "input contract must be (parameter (Syntax Type)) in pattern order");
                    if (!identifier(pattern->items[j + 1U]))
                        return fail(e, NLISP_PARSE_ERROR, pattern->items[j + 1U]->span, "invalid macro parameter identifier");
                    for (k = 0U; k < j; k++)
                        if (strcmp(pattern->items[k + 1U]->atom, pattern->items[j + 1U]->atom) == 0)
                            return fail(e, NLISP_PARSE_ERROR, c->span, "duplicate macro parameter");
                    m->inputs[j] = parse_type(a, c->items[1]->items[1], e);
                    if (m->inputs[j] == NULL) return false;
                }
                m->output = parse_type(a, output->items[1], e);
                if (m->output == NULL) return false;
                m->next = a->macros; a->macros = m;
            }
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

static SExpr *macro_node(Arena *a, Span span, Error *e) {
    if (a->generated_nodes >= a->limits.max_generated_nodes) {
        (void)fail(e, NLISP_UNKNOWN, span, "Unknown: generated-node limit (%zu) exceeded", a->limits.max_generated_nodes);
        return NULL;
    }
    a->generated_nodes++;
    return (SExpr *)aalloc(a, sizeof(SExpr));
}

static SExpr *copy_template_inner(Arena *a, Macro *m, SExpr *x, SExpr **args, Rename *renames, Error *e);

static SExpr *copy_template(Arena *a, Macro *m, SExpr *x, SExpr **args, Rename *renames, Error *e) {
    SExpr *result;
    if (a->copy_depth >= a->limits.max_expansion_depth) {
        (void)fail(e, NLISP_UNKNOWN, x->span, "Unknown: template depth limit (%zu) exceeded", a->limits.max_expansion_depth);
        return NULL;
    }
    a->copy_depth++;
    result = copy_template_inner(a, m, x, args, renames, e);
    a->copy_depth--;
    return result;
}

static SExpr *copy_template(Arena *a, Macro *m, SExpr *x, SExpr **args, Rename *renames, Error *e);

static bool next_fresh_scope(Arena *a, Span span, size_t *scope, Error *e) {
    if (a->fresh_scope >= (SIZE_MAX - 2U) / 3U)
        return fail(e, NLISP_UNKNOWN, span, "Unknown: generated binding identity range exhausted");
    a->fresh_scope++;
    *scope = a->fresh_scope;
    return true;
}

static SExpr *fresh_value_atom(Arena *a, const SExpr *source, Error *e) {
    char buffer[80];
    size_t scope;
    SExpr *result = macro_node(a, source->span, e);
    if (result == NULL) return NULL;
    *result = *source;
    if (!next_fresh_scope(a, source->span, &scope, e)) return NULL;
    (void)snprintf(buffer, sizeof(buffer), "#%%nlisp%zu", scope);
    result->atom = astr(a, buffer, strlen(buffer)); result->origin = NULL; result->expanded = NULL;
    result->token_identity = name_identity(a, result->atom); result->resolved_identity = 0U;
    return result;
}

static SExpr *copy_binder(Arena *a, Macro *m, SExpr *x, Rename **renames, Error *e) {
    SExpr *r;
    Rename *name;
    size_t ignored;
    size_t scope;
    char buffer[80];
    if (!identifier(x) || macro_parameter(m, x->atom, &ignored)) {
        (void)fail(e, NLISP_PARSE_ERROR, x->span, "invalid template binding identifier; macro holes cannot occur in binding positions");
        return NULL;
    }
    r = macro_node(a, x->span, e); if (r == NULL) return NULL; *r = *x;
    if (!next_fresh_scope(a, x->span, &scope, e)) return NULL;
    (void)snprintf(buffer, sizeof(buffer), "#%%nlisp%zu", scope);
    r->atom = astr(a, buffer, strlen(buffer));
    r->token_identity = name_identity(a, r->atom); r->resolved_identity = 0U;
    name = (Rename *)aalloc(a, sizeof(*name));
    name->from = x->atom; name->to = r->atom; name->next = *renames; *renames = name;
    return r;
}

static SExpr *copy_template_inner(Arena *a, Macro *m, SExpr *x, SExpr **args, Rename *renames, Error *e) {
    SExpr *r;
    size_t i, index;
    Rename *name;
    if (x->kind == SX_ATOM) {
        for (name = renames; name != NULL; name = name->next) if (strcmp(name->from, x->atom) == 0) {
            r = macro_node(a, x->span, e); if (r == NULL) return NULL; *r = *x; r->atom = name->to; r->token_identity = name_identity(a, r->atom); r->resolved_identity = 0U; return r;
        }
        if (macro_parameter(m, x->atom, &index)) return args[index];
        r = macro_node(a, x->span, e); if (r == NULL) return NULL; *r = *x; r->origin = m; return r;
    }
    r = macro_node(a, x->span, e); if (r == NULL) return NULL; *r = *x;
    r->items = (SExpr **)aalloc(a, x->count * sizeof(*r->items));
    for (i = 0U; i < x->count; i++) r->items[i] = x->items[i];
    if (x->count > 0U && x->items[0]->kind == SX_ATOM &&
        !macro_parameter(m, x->items[0]->atom, &index)) {
        Macro *known;
        for (known = a->macros; known != NULL; known = known->next) if (strcmp(known->name, x->items[0]->atom) == 0) break;
        if (known != NULL) {
            SExpr *head = macro_node(a, x->items[0]->span, e);
            if (head == NULL) return NULL;
            *head = *x->items[0]; head->origin = m; head->resolved_identity = 0U;
            r->items[0] = head;
            for (i = 1U; i < x->count; i++) {
                r->items[i] = copy_template(a, m, x->items[i], args, renames, e);
                if (r->items[i] == NULL) return NULL;
            }
            return r;
        }
    }
    if (x->count == 4U && is_atom(x->items[0], "lambda") && x->items[1]->kind == SX_LIST) {
        SExpr *ps = macro_node(a, x->span, e); if (ps == NULL) return NULL; *ps = *x->items[1];
        ps->items = (SExpr **)aalloc(a, ps->count * sizeof(*ps->items));
        for (i = 0U; i < ps->count; i++) {
            SExpr *p = x->items[1]->items[i], *q;
            if (p->kind != SX_LIST || p->count != 2U) {
                (void)fail(e, NLISP_PARSE_ERROR, p->span, "invalid template lambda parameter"); return NULL;
            }
            {
                size_t j;
                for (j = 0U; j < i; j++) if (p->items[0]->kind == SX_ATOM &&
                    x->items[1]->items[j]->items[0]->kind == SX_ATOM &&
                    strcmp(x->items[1]->items[j]->items[0]->atom, p->items[0]->atom) == 0) {
                    (void)fail(e, NLISP_PARSE_ERROR, p->span, "duplicate template parameter identifier"); return NULL;
                }
            }
            q = macro_node(a, x->span, e); if (q == NULL) return NULL; *q = *p;
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
        SExpr *bs = macro_node(a, x->span, e); if (bs == NULL) return NULL; Rename *body_names = renames;
        *bs = *x->items[1]; bs->items = (SExpr **)aalloc(a, bs->count * sizeof(*bs->items));
        for (i = 0U; i < bs->count; i++) {
            SExpr *b = x->items[1]->items[i], *q, *d;
            if (b->kind != SX_LIST || b->count != 2U || b->items[0]->kind != SX_LIST || b->items[0]->count != 2U) {
                (void)fail(e, NLISP_PARSE_ERROR, b->span, "invalid template let binding"); return NULL;
            }
            {
                size_t j;
                for (j = 0U; j < i; j++) if (b->items[0]->items[0]->kind == SX_ATOM &&
                    x->items[1]->items[j]->items[0]->items[0]->kind == SX_ATOM &&
                    strcmp(x->items[1]->items[j]->items[0]->items[0]->atom, b->items[0]->items[0]->atom) == 0) {
                    (void)fail(e, NLISP_PARSE_ERROR, b->span, "duplicate template let identifier"); return NULL;
                }
            }
            q = macro_node(a, x->span, e); if (q == NULL) return NULL; *q = *b;
            q->items = (SExpr **)aalloc(a, 2U * sizeof(*q->items));
            d = macro_node(a, x->span, e); if (d == NULL) return NULL; *d = *b->items[0];
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
            q = macro_node(a, x->span, e); if (q == NULL) return NULL; *q = *c;
            q->items = (SExpr **)aalloc(a, 2U * sizeof(*q->items));
            p = macro_node(a, x->span, e); if (p == NULL) return NULL; *p = *c->items[0];
            p->items = (SExpr **)aalloc(a, p->count * sizeof(*p->items));
            if (p->count > 0U) p->items[0] = c->items[0]->items[0];
            for (j = 1U; j < p->count; j++) {
                size_t k;
                for (k = 1U; k < j; k++) if (c->items[0]->items[j]->kind == SX_ATOM &&
                    c->items[0]->items[k]->kind == SX_ATOM &&
                    strcmp(c->items[0]->items[j]->atom, c->items[0]->items[k]->atom) == 0) {
                    (void)fail(e, NLISP_PARSE_ERROR, c->span, "duplicate template pattern identifier"); return NULL;
                }
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

static bool integer_atom(const char *s) {
    const char *p = s;
    if (*p == '-') p++;
    if (*p == '0') return p[1] == '\0';
    if (*p < '1' || *p > '9') return false;
    do { p++; } while (*p >= '0' && *p <= '9');
    return *p == '\0';
}

static bool ascii_digit(char c) { return c >= '0' && c <= '9'; }

static uint64_t mpz_u64(const mpz_t value) {
    uint64_t result = 0U;
    size_t words = 0U;
    mpz_export(&result, &words, -1, sizeof(result), 0, 0U, value);
    return result;
}

static uint64_t round_ratio_scaled(const mpz_t numerator, const mpz_t denominator, int scale) {
    mpz_t scaled_numerator, scaled_denominator, quotient, remainder, twice_remainder;
    uint64_t result;
    mpz_inits(scaled_numerator, scaled_denominator, quotient, remainder, twice_remainder, NULL);
    mpz_set(scaled_numerator, numerator);
    mpz_set(scaled_denominator, denominator);
    if (scale < 0) mpz_mul_2exp(scaled_numerator, scaled_numerator, (mp_bitcnt_t)(-scale));
    else if (scale > 0) mpz_mul_2exp(scaled_denominator, scaled_denominator, (mp_bitcnt_t)scale);
    mpz_tdiv_qr(quotient, remainder, scaled_numerator, scaled_denominator);
    mpz_mul_2exp(twice_remainder, remainder, 1U);
    if (mpz_cmp(twice_remainder, scaled_denominator) > 0 ||
        (mpz_cmp(twice_remainder, scaled_denominator) == 0 && mpz_odd_p(quotient)))
        mpz_add_ui(quotient, quotient, 1U);
    result = mpz_u64(quotient);
    mpz_clears(scaled_numerator, scaled_denominator, quotient, remainder, twice_remainder, NULL);
    return result;
}

static double decimal_to_binary64(const char *digits, size_t digit_count, size_t first_nonzero,
                                  size_t fractional_digits, int64_t explicit_exponent, bool negative) {
    mpz_t significand, numerator, denominator, power;
    size_t i;
    int64_t decimal_exponent, decimal_order;
    int binary_exponent;
    uint64_t bits, rounded;
    double result;
    if (first_nonzero == digit_count) {
        bits = negative ? UINT64_C(0x8000000000000000) : 0U;
        memcpy(&result, &bits, sizeof(result));
        return result;
    }
    /* Outside this decimal range the result is certainly infinity or signed zero.
       These guards also keep exponent arithmetic bounded before constructing powers. */
    if (fractional_digits > (size_t)INT64_MAX) {
        bits = negative ? UINT64_C(0x8000000000000000) : 0U;
        memcpy(&result, &bits, sizeof(result));
        return result;
    }
    if (explicit_exponent < 0 && explicit_exponent < INT64_MIN + (int64_t)fractional_digits)
        decimal_exponent = INT64_MIN;
    else decimal_exponent = explicit_exponent - (int64_t)fractional_digits;
    if (digit_count - first_nonzero - 1U > (size_t)INT64_MAX) {
        bits = UINT64_C(0x7ff0000000000000);
        if (negative) bits |= UINT64_C(0x8000000000000000);
        memcpy(&result, &bits, sizeof(result));
        return result;
    }
    if (decimal_exponent > INT64_MAX - (int64_t)(digit_count - first_nonzero - 1U))
        decimal_order = INT64_MAX;
    else decimal_order = (int64_t)(digit_count - first_nonzero - 1U) + decimal_exponent;
    if (decimal_order > 400) {
        bits = UINT64_C(0x7ff0000000000000) | (negative ? UINT64_C(0x8000000000000000) : 0U);
        memcpy(&result, &bits, sizeof(result));
        return result;
    }
    if (decimal_order < -400) {
        bits = negative ? UINT64_C(0x8000000000000000) : 0U;
        memcpy(&result, &bits, sizeof(result));
        return result;
    }
    mpz_inits(significand, numerator, denominator, power, NULL);
    mpz_set_ui(significand, 0U);
    for (i = first_nonzero; i < digit_count; i++) {
        mpz_mul_ui(significand, significand, 10U);
        mpz_add_ui(significand, significand, (unsigned long)(digits[i] - '0'));
    }
    mpz_set(numerator, significand);
    mpz_set_ui(denominator, 1U);
    if (decimal_exponent >= 0) {
        if ((uint64_t)decimal_exponent > (uint64_t)ULONG_MAX) {
            bits = UINT64_C(0x7ff0000000000000);
            if (negative) bits |= UINT64_C(0x8000000000000000);
            memcpy(&result, &bits, sizeof(result));
            mpz_clears(significand, numerator, denominator, power, NULL);
            return result;
        }
        mpz_ui_pow_ui(power, 10U, (unsigned long)decimal_exponent);
        mpz_mul(numerator, numerator, power);
    } else {
        uint64_t magnitude = (uint64_t)(-(decimal_exponent + 1)) + 1U;
        if (magnitude > (uint64_t)ULONG_MAX) {
            bits = negative ? UINT64_C(0x8000000000000000) : 0U;
            memcpy(&result, &bits, sizeof(result));
            mpz_clears(significand, numerator, denominator, power, NULL);
            return result;
        }
        mpz_ui_pow_ui(denominator, 10U, (unsigned long)magnitude);
    }

    {
        size_t numerator_bits = mpz_sizeinbase(numerator, 2U);
        size_t denominator_bits = mpz_sizeinbase(denominator, 2U);
        int64_t difference;
        if (numerator_bits > (size_t)INT64_MAX || denominator_bits > (size_t)INT64_MAX) {
            bits = numerator_bits > denominator_bits ? UINT64_C(0x7ff0000000000000) : 0U;
            if (negative) bits |= UINT64_C(0x8000000000000000);
            memcpy(&result, &bits, sizeof(result));
            mpz_clears(significand, numerator, denominator, power, NULL);
            return result;
        }
        difference = (int64_t)numerator_bits - (int64_t)denominator_bits;
        if (difference > INT_MAX || difference < INT_MIN) {
            bits = difference > 0 ? UINT64_C(0x7ff0000000000000) : 0U;
            if (negative) bits |= UINT64_C(0x8000000000000000);
            memcpy(&result, &bits, sizeof(result));
            mpz_clears(significand, numerator, denominator, power, NULL);
            return result;
        }
        binary_exponent = (int)difference;
    }
    if (binary_exponent >= 0) {
        mpz_mul_2exp(power, denominator, (mp_bitcnt_t)binary_exponent);
        if (mpz_cmp(numerator, power) < 0) binary_exponent--;
    } else {
        mpz_mul_2exp(power, numerator, (mp_bitcnt_t)(-binary_exponent));
        if (mpz_cmp(power, denominator) < 0) binary_exponent--;
    }
    if (binary_exponent > 1023) {
        bits = UINT64_C(0x7ff0000000000000);
        rounded = 0U;
    } else if (binary_exponent < -1022) {
        rounded = round_ratio_scaled(numerator, denominator, -1074);
        bits = rounded >= (UINT64_C(1) << 52U) ? (UINT64_C(1) << 52U) : rounded;
    } else {
        rounded = round_ratio_scaled(numerator, denominator, binary_exponent - 52);
        if (rounded == (UINT64_C(1) << 53U)) {
            rounded >>= 1U;
            binary_exponent++;
        }
        if (binary_exponent > 1023) bits = UINT64_C(0x7ff0000000000000);
        else bits = ((uint64_t)(binary_exponent + 1023) << 52U) |
                    (rounded - (UINT64_C(1) << 52U));
    }
    if (negative) bits |= UINT64_C(0x8000000000000000);
    memcpy(&result, &bits, sizeof(result));
    mpz_clears(significand, numerator, denominator, power, NULL);
    return result;
}

static bool float_atom(const char *s, double *out) {
    const char *p = s;
    const char *digits_start;
    char *digits;
    size_t digit_count = 0U, fractional_digits = 0U, first_nonzero;
    int64_t exponent = 0;
    bool negative = false;
    if (*p == '-') p++;
    negative = s[0] == '-';
    if (!ascii_digit(*p)) return false;
    digits_start = p;
    while (ascii_digit(*p)) { p++; digit_count++; }
    if (*p++ != '.' || !ascii_digit(*p)) return false;
    while (ascii_digit(*p)) { p++; digit_count++; fractional_digits++; }
    if (*p == 'e' || *p == 'E') {
        bool exponent_negative = false;
        p++;
        if (*p == '+' || *p == '-') { exponent_negative = *p == '-'; p++; }
        if (!ascii_digit(*p)) return false;
        while (ascii_digit(*p)) {
            int digit = *p++ - '0';
            if (exponent > (INT64_MAX - digit) / 10) exponent = INT64_MAX;
            else exponent = exponent * 10 + digit;
        }
        if (exponent_negative) exponent = -exponent;
    }
    if (*p != '\0') return false;
    digits = (char *)malloc(digit_count + 1U);
    if (digits == NULL) { fputs("nlisp: out of memory\n", stderr); abort(); }
    memcpy(digits, digits_start, (size_t)(strchr(s, '.') - digits_start));
    {
        size_t whole = (size_t)(strchr(s, '.') - digits_start);
        size_t fraction = digit_count - whole;
        memcpy(digits + whole, strchr(s, '.') + 1, fraction);
        digits[digit_count] = '\0';
    }
    first_nonzero = 0U;
    while (first_nonzero < digit_count && digits[first_nonzero] == '0') first_nonzero++;
    *out = decimal_to_binary64(digits, digit_count, first_nonzero, fractional_digits, exponent, negative);
    free(digits);
    return true;
}

static bool require(const Type *got, const Type *want, Span span, Error *e, const char *where) {
    char a[256], b[256];
    if (type_eq(got, want)) return true;
    type_text(got, a, sizeof(a)); type_text(want, b, sizeof(b));
    return fail(e, NLISP_TYPE_ERROR, span, "%s: expected %s, got %s", where, b, a);
}

static Type *check_expr(Arena *a, const SExpr *x, TBind *env, Error *e);

static Type *check_macro_call(Arena *a, const SExpr *x, Macro *m, TBind *env, Error *e) {
    size_t i, call_id = 0U, fresh_start, fresh_end;
    Type *got;
    SExpr *expanded;
    if (x->count - 1U != m->arity) {
        (void)fail(e, NLISP_TYPE_ERROR, x->span, "macro '%s' expects %zu arguments", m->name, m->arity); return NULL;
    }
    if (!a->checking_templates) {
        if (a->expansions >= a->limits.max_expansions) {
            (void)fail(e, NLISP_UNKNOWN, x->span, "Unknown: macro expansion limit (%zu) exceeded at '%s'", a->limits.max_expansions, m->name);
            return NULL;
        }
        a->expansions++; call_id = a->expansions;
    }
    for (i = 0U; i < m->arity; i++) {
        got = check_expr(a, x->items[i + 1U], env, e);
        if (got == NULL || !require(got, m->inputs[i], x->items[i + 1U]->span, e, "macro input contract"))
            return NULL;
    }
    /* A definition is checked against referenced macros' declared contracts.
       Actual calls must complete their expansion and are checked afterwards. */
    if (a->checking_templates) return m->output;
    fresh_start = a->fresh_scope;
    expanded = copy_template(a, m, m->template_expr, x->items + 1U, NULL, e);
    fresh_end = a->fresh_scope;
    if (expanded == NULL) return NULL;
    got = check_expr(a, expanded, env, e);
    if (got == NULL || !require(got, m->output, x->span, e, "macro output contract")) return NULL;
    ((SExpr *)x)->expanded = expanded;
    if (a->capture_trace) {
        MacroTrace *trace = (MacroTrace *)aalloc(a, sizeof(*trace));
        trace->definition = m; trace->input = x; trace->substitution = expanded; trace->call_id = call_id; trace->fresh_start = fresh_start; trace->fresh_end = fresh_end;
        if (a->trace_tail != NULL) a->trace_tail->next = trace; else a->trace_head = trace;
        a->trace_tail = trace; a->trace_count++;
    }
    return got;
}

static bool prepare_macros(Arena *a, Macro *m, size_t index, TBind *env, Error *e) {
    SExpr **holes, *template_expr;
    TBind *local = env;
    Type *got;
    size_t i;
    if (m == NULL) return true;
    if (m->declaration_index != index) return true;
    if (tlookup(env, m->name) != NULL)
        return fail(e, NLISP_TYPE_ERROR, m->pattern->span, "macro name conflicts with value '%s'", m->name);
    holes = (SExpr **)aalloc(a, m->arity * sizeof(*holes));
    for (i = 0U; i < m->arity; i++) {
        holes[i] = fresh_value_atom(a, m->pattern->items[i + 1U], e);
        if (holes[i] == NULL) return false;
        local = tbind(a, local, holes[i]->atom, m->inputs[i]);
    }
    m->type_env = env;
    template_expr = copy_template(a, m, m->template_expr, holes, NULL, e);
    if (template_expr == NULL) return false;
    got = check_expr(a, template_expr, local, e);
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
        {
            size_t j;
            if (!identifier(b->items[0]->items[0])) {
                (void)fail(e, NLISP_PARSE_ERROR, b->span, "invalid let binding identifier"); return NULL;
            }
            for (j = 0U; j < i; j++) if (strcmp(names[j], b->items[0]->items[0]->atom) == 0) {
                (void)fail(e, NLISP_PARSE_ERROR, b->span, "duplicate let binding identifier"); return NULL;
            }
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
    {
        const SExpr *pattern = full->items[0];
        size_t j;
        for (j = 1U; j < pattern->count; j++) if (!identifier(pattern->items[j])) {
            (void)fail(e, NLISP_PARSE_ERROR, pattern->items[j]->span, "invalid pattern binding identifier"); return NULL;
        }
        if (pattern->count == 3U && strcmp(pattern->items[1]->atom, pattern->items[2]->atom) == 0) {
            (void)fail(e, NLISP_PARSE_ERROR, pattern->span, "duplicate pattern binding identifier"); return NULL;
        }
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

static Type *check_expr_inner(Arena *a, const SExpr *x, TBind *env, Error *e);

static Type *check_expr(Arena *a, const SExpr *x, TBind *env, Error *e) {
    Type *result;
    if (a->check_depth >= a->limits.max_expansion_depth || a->check_steps >= a->limits.max_check_steps) {
        (void)fail(e, NLISP_UNKNOWN, x->span, "Unknown: %s limit (%zu) exceeded",
                   a->check_depth >= a->limits.max_expansion_depth ? "expanded expression depth" : "type-check work",
                   a->check_depth >= a->limits.max_expansion_depth ? a->limits.max_expansion_depth : a->limits.max_check_steps);
        return NULL;
    }
    a->check_steps++; a->check_depth++;
    result = check_expr_inner(a, x, env, e);
    a->check_depth--;
    return result;
}

static Type *check_expr_inner(Arena *a, const SExpr *x, TBind *env, Error *e) {
    double ignored_float;
    if (x->expanded != NULL) return check_expr(a, x->expanded, env, e);
    if (x->kind == SX_ATOM) {
        Type *t;
        if (x->atom[0] == '"') return type_new(a, TY_STRING);
        if (x->atom[0] == '#' && x->atom[1] == '\\') return type_new(a, TY_CHAR);
        if (strcmp(x->atom, "true") == 0 || strcmp(x->atom, "false") == 0) return type_new(a, TY_BOOL);
        if (strcmp(x->atom, "unit") == 0) return type_new(a, TY_UNIT);
        if (integer_atom(x->atom)) return type_new(a, TY_INT);
        if (float_atom(x->atom, &ignored_float)) return type_new(a, TY_FLOAT);
        if (x->origin != NULL && !a->checking_templates) {
            TBind *binding = tfind(x->origin->type_env, x->atom);
            if (binding != NULL && binding->value_index != SIZE_MAX && binding->value_index >= a->check_index) {
                (void)fail(e, NLISP_TYPE_ERROR, x->span, "macro requires value '%s' before its initialization", x->atom);
                return NULL;
            }
        }
        {
            TBind *environment = x->origin == NULL ? env : x->origin->type_env;
            TBind *selected = tfind(environment, x->atom);
            t = selected == NULL ? NULL : selected->type;
            ((SExpr *)x)->resolved_identity = selected == NULL ? 0U : selected->identity;
            if (selected != NULL && !observe_name(a, x->atom, environment, selected, x->span,
                    x->origin == NULL ? SIZE_MAX : x->origin->declaration_index, e)) return NULL;
        }
        if (t == NULL) (void)fail(e, NLISP_TYPE_ERROR, x->span, "unbound identifier '%s'", x->atom);
        return t;
    }
    if (x->count == 0U) { (void)fail(e, NLISP_PARSE_ERROR, x->span, "empty list is not an expression"); return NULL; }
    if (x->items[0]->kind == SX_ATOM && x->items[0]->resolved_identity == 0U) {
        Macro *m;
        bool found = false;
        for (m = a->macros; m != NULL; m = m->next)
            if (strcmp(m->name, x->items[0]->atom) == 0) {
                found = true;
                if (m->arity == x->count - 1U) return check_macro_call(a, x, m, env, e);
            }
        if (found) {
            (void)fail(e, NLISP_TYPE_ERROR, x->span, "no macro rule for '%s' with %zu arguments", x->items[0]->atom, x->count - 1U);
            return NULL;
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

typedef enum {
    BI_ADD, BI_SUB, BI_MUL, BI_LT, BI_LE, BI_GT, BI_GE, BI_EQ,
    BI_QUOTIENT, BI_REMAINDER, BI_BOOL_EQ, BI_NOT,
    BI_FADD, BI_FSUB, BI_FMUL, BI_FDIV, BI_FLT, BI_FLE, BI_FGT, BI_FGE, BI_FEQ,
    BI_TO_FLOAT, BI_TRUNCATE, BI_STRING_EQ, BI_STRING_APPEND, BI_CHAR_EQ
} Builtin;

typedef struct {
    const char *name;
    Builtin operation;
    TypeKind input, output;
    size_t arity;
    bool optional;
} BuiltinSpec;

static const BuiltinSpec builtin_specs[] = {
    {"+", BI_ADD, TY_INT, TY_INT, 2U, false},
    {"-", BI_SUB, TY_INT, TY_INT, 2U, false},
    {"*", BI_MUL, TY_INT, TY_INT, 2U, false},
    {"<", BI_LT, TY_INT, TY_BOOL, 2U, false},
    {"<=", BI_LE, TY_INT, TY_BOOL, 2U, false},
    {">", BI_GT, TY_INT, TY_BOOL, 2U, false},
    {">=", BI_GE, TY_INT, TY_BOOL, 2U, false},
    {"integer=", BI_EQ, TY_INT, TY_BOOL, 2U, false},
    {"quotient", BI_QUOTIENT, TY_INT, TY_INT, 2U, true},
    {"remainder", BI_REMAINDER, TY_INT, TY_INT, 2U, true},
    {"boolean=", BI_BOOL_EQ, TY_BOOL, TY_BOOL, 2U, false},
    {"not", BI_NOT, TY_BOOL, TY_BOOL, 1U, false},
    {"float+", BI_FADD, TY_FLOAT, TY_FLOAT, 2U, false},
    {"float-", BI_FSUB, TY_FLOAT, TY_FLOAT, 2U, false},
    {"float*", BI_FMUL, TY_FLOAT, TY_FLOAT, 2U, false},
    {"float/", BI_FDIV, TY_FLOAT, TY_FLOAT, 2U, false},
    {"float<", BI_FLT, TY_FLOAT, TY_BOOL, 2U, false},
    {"float<=", BI_FLE, TY_FLOAT, TY_BOOL, 2U, false},
    {"float>", BI_FGT, TY_FLOAT, TY_BOOL, 2U, false},
    {"float>=", BI_FGE, TY_FLOAT, TY_BOOL, 2U, false},
    {"float=", BI_FEQ, TY_FLOAT, TY_BOOL, 2U, false},
    {"to-float", BI_TO_FLOAT, TY_INT, TY_FLOAT, 1U, false},
    {"float-truncate", BI_TRUNCATE, TY_FLOAT, TY_INT, 1U, true},
    {"string=", BI_STRING_EQ, TY_STRING, TY_BOOL, 2U, false},
    {"string-append", BI_STRING_APPEND, TY_STRING, TY_STRING, 2U, false},
    {"character=", BI_CHAR_EQ, TY_CHAR, TY_BOOL, 2U, false}
};

static TBind *type_builtins(Arena *a) {
    TBind *env = NULL;
    size_t i, j;
    for (i = 0U; i < sizeof(builtin_specs) / sizeof(builtin_specs[0]); i++) {
        const BuiltinSpec *spec = &builtin_specs[i];
        Type **ps = (Type **)aalloc(a, spec->arity * sizeof(*ps));
        Type *result = type_new(a, spec->output);
        for (j = 0U; j < spec->arity; j++) ps[j] = type_new(a, spec->input);
        if (spec->optional) {
            Type *option = type_new(a, TY_OPTION); option->elem = result; result = option;
        }
        register_identity(a, spec->name, 3U * (i + 1U));
        env = tbind(a, env, spec->name, type_fun(a, ps, spec->arity, result));
    }
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
    {
        TBind *scope = env;
        for (i = 0U; i <= p->count; i++) {
            Macro *m;
            for (m = a->macros; m != NULL; m = m->next)
                if (m->declaration_index == i) m->type_env = scope;
            if (i < p->count && p->data[i].kind == D_VAL) {
                scope = tbind(a, scope, p->data[i].as.val.name, p->data[i].as.val.type);
                scope->value_index = i;
            }
        }
        a->checking_templates = true;
        for (i = 0U; i <= p->count; i++) {
            for (Macro *m = a->macros; m != NULL; m = m->next) {
                if (m->declaration_index == i &&
                    !prepare_macros(a, m, i, m->type_env, e)) return false;
            }
        }
        a->checking_templates = false;
    }
    for (i = 0U; i < p->count; i++) {
        a->check_index = i;
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
typedef enum { V_BOOL, V_INT, V_UNIT, V_FLOAT, V_STRING, V_CHAR, V_CLOSURE, V_BUILTIN, V_NIL, V_CONS, V_NONE, V_SOME } VKind;
typedef struct { Param *params; size_t arity; SExpr *body; RBind *env; } Closure;
struct Value {
    VKind kind;
    union {
        bool boolean; mpz_t integer; double floating; Text text; uint32_t character; Closure closure; Builtin builtin;
        struct { Value *head, *tail; } cons; Value *some;
    } as;
};
struct RBind { const char *name; Value *value; RBind *next; };
typedef struct { Arena *a; Error *e; } Runtime;

static void clear_integer(void *ptr) { mpz_clear(((Value *)ptr)->as.integer); }
static Value *vnew(Runtime *r, VKind k) {
    Value *v = (Value *)aalloc(r->a, sizeof(*v));
    v->kind = k;
    if (k == V_INT) { mpz_init(v->as.integer); r->a->head->cleanup = clear_integer; }
    return v;
}

static RBind *rbind(Runtime *r, RBind *env, const char *name, Value *v) {
    RBind *b = (RBind *)aalloc(r->a, sizeof(*b)); b->name = name; b->value = v; b->next = env; return b;
}
static RBind *rfind(RBind *env, const char *name) {
    for (; env != NULL; env = env->next) if (strcmp(env->name, name) == 0) return env;
    return NULL;
}
static Value *rlookup(RBind *env, const char *name) {
    RBind *binding = rfind(env, name);
    return binding == NULL ? NULL : binding->value;
}

/* GMP's mpz_get_d truncates. Round the discarded magnitude bits explicitly
   to nearest, ties to even before converting the exact 53-bit significand. */
static double integer_to_float(const mpz_t value) {
    mpz_t magnitude, significand;
    size_t bits, shift;
    double result;
    int sign = mpz_sgn(value);
    if (sign == 0) return 0.0;
    mpz_init(magnitude); mpz_abs(magnitude, value);
    bits = mpz_sizeinbase(magnitude, 2);
    if (bits <= 53U) { result = mpz_get_d(value); mpz_clear(magnitude); return result; }
    if (bits > 1024U) { mpz_clear(magnitude); return sign < 0 ? -INFINITY : INFINITY; }
    shift = bits - 53U;
    mpz_init(significand); mpz_fdiv_q_2exp(significand, magnitude, (mp_bitcnt_t)shift);
    if (mpz_tstbit(magnitude, (mp_bitcnt_t)(shift - 1U)) &&
        (mpz_scan1(magnitude, 0U) < shift - 1U || mpz_odd_p(significand)))
        mpz_add_ui(significand, significand, 1U);
    result = ldexp(mpz_get_d(significand), (int)shift);
    mpz_clear(significand); mpz_clear(magnitude);
    return sign < 0 ? -result : result;
}

static Value *eval(Runtime *r, const SExpr *x, RBind *env);

static Value *apply(Runtime *r, Value *f, Value **args, size_t n, Span span) {
    size_t i; RBind *local; Value *v;
    if (f->kind == V_BUILTIN) {
        if (f->as.builtin == BI_STRING_EQ || f->as.builtin == BI_STRING_APPEND || f->as.builtin == BI_CHAR_EQ) {
            VKind expected = f->as.builtin == BI_CHAR_EQ ? V_CHAR : V_STRING;
            if (n != 2U || args[0]->kind != expected || args[1]->kind != expected) {
                (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "internal text builtin type error"); return NULL;
            }
            if (f->as.builtin == BI_STRING_APPEND) {
                Text left = args[0]->as.text, right = args[1]->as.text;
                if (left.length > SIZE_MAX - right.length - 1U) {
                    (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "String size overflow"); return NULL;
                }
                v = vnew(r, V_STRING); v->as.text.length = left.length + right.length;
                v->as.text.data = (char *)aalloc(r->a, v->as.text.length + 1U);
                memcpy(v->as.text.data, left.data, left.length);
                memcpy(v->as.text.data + left.length, right.data, right.length); return v;
            }
            v = vnew(r, V_BOOL);
            v->as.boolean = expected == V_CHAR ? args[0]->as.character == args[1]->as.character :
                args[0]->as.text.length == args[1]->as.text.length &&
                memcmp(args[0]->as.text.data, args[1]->as.text.data, args[0]->as.text.length) == 0;
            return v;
        }
        if (f->as.builtin == BI_TO_FLOAT) {
            if (n != 1U || args[0]->kind != V_INT) {
                (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "internal conversion type error"); return NULL;
            }
            v = vnew(r, V_FLOAT); v->as.floating = integer_to_float(args[0]->as.integer); return v;
        }
        if (f->as.builtin == BI_TRUNCATE) {
            double input;
            if (n != 1U || args[0]->kind != V_FLOAT) {
                (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "internal conversion type error"); return NULL;
            }
            input = args[0]->as.floating;
            if (!isfinite(input)) return vnew(r, V_NONE);
            v = vnew(r, V_SOME); v->as.some = vnew(r, V_INT);
            mpz_set_d(v->as.some->as.integer, input); return v;
        }
        if (f->as.builtin >= BI_FADD && f->as.builtin <= BI_FEQ) {
            double left, right;
            if (n != 2U || args[0]->kind != V_FLOAT || args[1]->kind != V_FLOAT) {
                (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "internal Float builtin type error"); return NULL;
            }
            left = args[0]->as.floating; right = args[1]->as.floating;
            v = vnew(r, f->as.builtin <= BI_FDIV ? V_FLOAT : V_BOOL);
            switch (f->as.builtin) {
                case BI_FADD: v->as.floating = left + right; break;
                case BI_FSUB: v->as.floating = left - right; break;
                case BI_FMUL: v->as.floating = left * right; break;
                case BI_FDIV: v->as.floating = left / right; break;
                case BI_FLT: v->as.boolean = left < right; break;
                case BI_FLE: v->as.boolean = left <= right; break;
                case BI_FGT: v->as.boolean = left > right; break;
                case BI_FGE: v->as.boolean = left >= right; break;
                default: v->as.boolean = left == right; break;
            }
            return v;
        }
        if (f->as.builtin == BI_NOT || f->as.builtin == BI_BOOL_EQ) {
            size_t arity = f->as.builtin == BI_NOT ? 1U : 2U;
            if (n != arity || args[0]->kind != V_BOOL ||
                (arity == 2U && args[1]->kind != V_BOOL)) {
                (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "internal Boolean builtin type error"); return NULL;
            }
            v = vnew(r, V_BOOL);
            v->as.boolean = arity == 1U ? !args[0]->as.boolean :
                args[0]->as.boolean == args[1]->as.boolean;
            return v;
        }
        if (n != 2U || args[0]->kind != V_INT || args[1]->kind != V_INT) {
            (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "internal builtin type error"); return NULL;
        }
        if (f->as.builtin == BI_QUOTIENT || f->as.builtin == BI_REMAINDER) {
            if (mpz_sgn(args[1]->as.integer) == 0) return vnew(r, V_NONE);
            v = vnew(r, V_SOME); v->as.some = vnew(r, V_INT);
            if (f->as.builtin == BI_QUOTIENT)
                mpz_tdiv_q(v->as.some->as.integer, args[0]->as.integer, args[1]->as.integer);
            else mpz_tdiv_r(v->as.some->as.integer, args[0]->as.integer, args[1]->as.integer);
            return v;
        }
        if (f->as.builtin >= BI_LT && f->as.builtin <= BI_EQ) {
            int comparison = mpz_cmp(args[0]->as.integer, args[1]->as.integer);
            v = vnew(r, V_BOOL);
            switch (f->as.builtin) {
                case BI_LT: v->as.boolean = comparison < 0; break;
                case BI_LE: v->as.boolean = comparison <= 0; break;
                case BI_GT: v->as.boolean = comparison > 0; break;
                case BI_GE: v->as.boolean = comparison >= 0; break;
                default: v->as.boolean = comparison == 0; break;
            }
            return v;
        }
        v = vnew(r, V_INT);
        switch (f->as.builtin) {
            case BI_ADD: mpz_add(v->as.integer, args[0]->as.integer, args[1]->as.integer); break;
            case BI_SUB: mpz_sub(v->as.integer, args[0]->as.integer, args[1]->as.integer); break;
            case BI_MUL: mpz_mul(v->as.integer, args[0]->as.integer, args[1]->as.integer); break;
            default: (void)fail(r->e, NLISP_RUNTIME_ERROR, span, "unknown builtin"); return NULL;
        }
        return v;
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
    double floating;
    if (x->expanded != NULL) return eval(r, x->expanded, env);
    if (x->kind == SX_ATOM) {
        Value *v;
        if (x->atom[0] == '"') {
            v = vnew(r, V_STRING);
            if (!string_literal(r->a, x->atom, &v->as.text)) {
                (void)fail(r->e, NLISP_RUNTIME_ERROR, x->span, "invalid string literal"); return NULL;
            }
            return v;
        }
        if (x->atom[0] == '#' && x->atom[1] == '\\') {
            v = vnew(r, V_CHAR);
            if (!character_literal(x->atom, &v->as.character)) {
                (void)fail(r->e, NLISP_RUNTIME_ERROR, x->span, "invalid character literal"); return NULL;
            }
            return v;
        }
        if (strcmp(x->atom, "true") == 0 || strcmp(x->atom, "false") == 0) {
            v = vnew(r, V_BOOL); v->as.boolean = strcmp(x->atom, "true") == 0; return v;
        }
        if (strcmp(x->atom, "unit") == 0) return vnew(r, V_UNIT);
        if (integer_atom(x->atom)) { v = vnew(r, V_INT); (void)mpz_set_str(v->as.integer, x->atom, 10); return v; }
        if (float_atom(x->atom, &floating)) { v = vnew(r, V_FLOAT); v->as.floating = floating; return v; }
        {
            RBind *binding = rfind(x->origin == NULL ? env : x->origin->runtime_env, x->atom);
            if (binding == NULL) {
                (void)fail(r->e, NLISP_RUNTIME_ERROR, x->span, "internal unbound name"); return NULL;
            }
            if (binding->value == NULL) {
                (void)fail(r->e, NLISP_RUNTIME_ERROR, x->span,
                           "global value '%s' read before its initialization", x->atom); return NULL;
            }
            return binding->value;
        }
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
    size_t i;
    for (i = 0U; i < sizeof(builtin_specs) / sizeof(builtin_specs[0]); i++)
        env = bind_builtin(r, env, builtin_specs[i].name, builtin_specs[i].operation);
    return env;
}

static Value *run_program(Arena *a, Program *p, Error *e) {
    Runtime r = {a, e}; RBind *env = runtime_builtins(&r);
    Value **closures = (Value **)aalloc(a, p->count * sizeof(*closures));
    /* Like Program.data, value_slots is indexed by mixed declaration index.
       Each element points to the actual RBind cell inserted into env, not to
       a copy of its Value. This is the shared cell captured by closures. */
    RBind **value_slots = (RBind **)aalloc(a, p->count * sizeof(*value_slots));
    size_t count = 0U, i; Value *main_value;
    for (i = 0U; i < p->count; i++) if (p->data[i].kind == D_FUN) {
        FunDef *f = &p->data[i].as.fun; Value *v = vnew(&r, V_CLOSURE);
        v->as.closure = (Closure){f->params, f->arity, f->body, NULL};
        closures[count++] = v; env = rbind(&r, env, f->name, v);
    }
    /* Global bindings exist once for the whole execution. Closures retain
       these shared cells, including cells filled by a later initializer. */
    for (i = 0U; i < p->count; i++) if (p->data[i].kind == D_VAL) {
        env = rbind(&r, env, p->data[i].as.val.name, NULL);
        value_slots[i] = env;
    }
    for (i = 0U; i < count; i++) closures[i]->as.closure.env = env;
    for (i = 0U; i < p->count; i++) if (p->data[i].kind == D_VAL) {
        Value *v;
        Macro *m;
        for (m = a->macros; m != NULL; m = m->next)
            if (m->declaration_index <= i && m->runtime_env == NULL) m->runtime_env = env;
        v = eval(&r, p->data[i].as.val.init, env); if (v == NULL) return NULL;
        value_slots[i]->value = v;
    }
    {
        Macro *m;
        for (m = a->macros; m != NULL; m = m->next)
            if (m->runtime_env == NULL) m->runtime_env = env;
    }
    main_value = rlookup(env, "main");
    return apply(&r, main_value, NULL, 0U, (Span){1U, 1U});
}

static void print_value(FILE *out, const Value *v) {
    switch (v->kind) {
        case V_BOOL: fputs(v->as.boolean ? "true" : "false", out); break;
        case V_INT: (void)mpz_out_str(out, 10, v->as.integer); break;
        case V_FLOAT: (void)fprintf(out, "%.17g", v->as.floating); break;
        case V_STRING: {
            size_t i;
            fputc('"', out);
            for (i = 0U; i < v->as.text.length; i++) {
                unsigned char c = (unsigned char)v->as.text.data[i];
                if (c == '"' || c == '\\') { fputc('\\', out); fputc(c, out); }
                else if (c < 32U) (void)fprintf(out, "\\u{%x}", (unsigned int)c);
                else fputc(c, out);
            }
            fputc('"', out); break;
        }
        case V_CHAR: (void)fprintf(out, "#\\u{%x}", (unsigned int)v->as.character); break;
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

/* Unlike the human-readable expansion, this interchange retains the
   definition-site origin of each atom. Consumers must not discard it. */
static void print_json_string(FILE *out, const char *s) {
    fputc('"', out);
    for (; *s != '\0'; s++) {
        unsigned char c = (unsigned char)*s;
        if (c == '"' || c == '\\') { fputc('\\', out); fputc(c, out); }
        else if (c < 32U) (void)fprintf(out, "\\u%04x", (unsigned int)c);
        else fputc(c, out);
    }
    fputc('"', out);
}

static void print_core_json_mode(FILE *out, const SExpr *x, bool expanded) {
    size_t i;
    if (expanded && x->expanded != NULL) { print_core_json_mode(out, x->expanded, true); return; }
    if (x->kind == SX_ATOM) {
        fputs("{\"atom\":", out); print_json_string(out, x->atom);
        fputs(",\"origin\":", out);
        if (x->origin == NULL) fputs("null", out);
        else (void)fprintf(out, "%zu", x->origin->declaration_index);
        (void)fprintf(out, ",\"token_identity\":%zu,\"resolved_identity\":", x->token_identity);
        if (x->resolved_identity == 0U) fputs("null", out);
        else (void)fprintf(out, "%zu", x->resolved_identity);
        fputc('}', out); return;
    }
    fputc('[', out);
    for (i = 0U; i < x->count; i++) {
        if (i != 0U) fputc(',', out);
        print_core_json_mode(out, x->items[i], expanded);
    }
    fputc(']', out);
}

static void print_core_json(FILE *out, const SExpr *x) { print_core_json_mode(out, x, true); }

static void print_raw_forms(FILE *out, SExpr **forms, size_t count) {
    size_t i;
    fputc('[', out);
    for (i = 0U; i < count; i++) {
        if (i != 0U) fputc(',', out);
        print_core_json_mode(out, forms[i], false);
    }
    fputc(']', out);
}

static void print_name_entry(FILE *out, const TBind *binding) {
    fputs("{\"name\":", out); print_json_string(out, binding->name);
    (void)fprintf(out, ",\"identity\":%zu,\"type_tag\":%zu}", binding->identity, binding->type_tag);
}

static void print_name_observations(FILE *out, Arena *a) {
    NameObservation *observation;
    size_t index = 0U;
    fputs(",\"name_resolution\":[", out);
    for (observation = a->name_head; observation != NULL; observation = observation->next) {
        TBind *binding;
        bool first = true;
        if (index++ != 0U) fputc(',', out);
        fputs("{\"name\":", out); print_json_string(out, observation->name);
        (void)fprintf(out, ",\"line\":%zu,\"column\":%zu,\"definition_origin\":", observation->line, observation->column);
        if (observation->definition_index == SIZE_MAX) fputs("null", out);
        else (void)fprintf(out, "%zu", observation->definition_index);
        fputs(",\"environment\":[", out);
        for (binding = observation->environment; binding != NULL; binding = binding->next) {
            if (!first) fputc(',', out);
            first = false; print_name_entry(out, binding);
        }
        fputs("],\"selected\":", out); print_name_entry(out, observation->selected);
        fputc('}', out);
    }
    fputc(']', out);
}

static void print_export_limits(FILE *out, Arena *a) {
    fputs("\"limits\":{", out);
    (void)fprintf(out, "\"max_expansions\":%zu,\"max_generated_nodes\":%zu,\"max_expansion_depth\":%zu,\"max_check_steps\":%zu}",
                  a->limits.max_expansions, a->limits.max_generated_nodes, a->limits.max_expansion_depth, a->limits.max_check_steps);
}

static void print_process_evidence(FILE *out, Arena *a) {
    MacroTrace *trace;
    size_t sequence = 0U;
    fputc(',', out); print_export_limits(out, a);
    fputs(",\"source_ast\":", out); print_raw_forms(out, a->source_forms, a->source_count);
    fputs(",\"normalized_ast\":", out); print_raw_forms(out, a->normalized_forms, a->normalized_count);
    fputs(",\"macro_trace\":[", out);
    for (trace = a->trace_head; trace != NULL; trace = trace->next) {
        Macro *m = trace->definition;
        if (sequence != 0U) fputc(',', out);
        (void)fprintf(out, "{\"sequence\":%zu,\"call_id\":%zu,\"macro\":", sequence++, trace->call_id);
        print_json_string(out, m->name);
        (void)fprintf(out, ",\"definition_index\":%zu,\"arity\":%zu,\"line\":%zu,\"column\":%zu,\"rule\":",
                      m->declaration_index, m->arity, trace->input->span.line, trace->input->span.column);
        print_core_json_mode(out, m->rule, false);
        (void)fprintf(out, ",\"fresh_start\":%zu,\"fresh_end\":%zu", trace->fresh_start, trace->fresh_end);
        fputs(",\"input\":", out); print_core_json_mode(out, trace->input, false);
        fputs(",\"substitution\":", out); print_core_json_mode(out, trace->substitution, false);
        fputs(",\"result\":", out); print_core_json(out, trace->substitution);
        fputc('}', out);
    }
    fputc(']', out);
}

static bool expanded_size(Arena *a, SExpr *x, size_t depth, size_t *result, Error *e) {
    size_t size = 1U, height = 1U, i;
    if (depth >= a->limits.max_expansion_depth)
        return fail(e, NLISP_UNKNOWN, x->span, "Unknown: expanded tree depth limit (%zu) exceeded", a->limits.max_expansion_depth);
    if (x->logical_size != 0U) {
        if (x->logical_height > a->limits.max_expansion_depth - depth)
            return fail(e, NLISP_UNKNOWN, x->span, "Unknown: expanded tree depth limit (%zu) exceeded", a->limits.max_expansion_depth);
        *result = x->logical_size; return true;
    }
    if (x->expanded != NULL) {
        if (!expanded_size(a, x->expanded, depth + 1U, &size, e)) return false;
        height = x->expanded->logical_height + 1U;
    } else if (x->kind == SX_LIST) {
        for (i = 0U; i < x->count; i++) {
            size_t child;
            if (!expanded_size(a, x->items[i], depth + 1U, &child, e)) return false;
            if (x->items[i]->logical_height + 1U > height) height = x->items[i]->logical_height + 1U;
            if (child > a->limits.max_generated_nodes || size > a->limits.max_generated_nodes - child)
                return fail(e, NLISP_UNKNOWN, x->span, "Unknown: expanded tree node limit (%zu) exceeded", a->limits.max_generated_nodes);
            size += child;
        }
    }
    if (size > a->limits.max_generated_nodes)
        return fail(e, NLISP_UNKNOWN, x->span, "Unknown: expanded tree node limit (%zu) exceeded", a->limits.max_generated_nodes);
    x->logical_size = size; x->logical_height = height; *result = size; return true;
}

static bool expanded_program_size(Arena *a, Forms forms, Error *e) {
    size_t total = 0U, i;
    for (i = 0U; i < forms.count; i++) {
        size_t size;
        if (!expanded_size(a, forms.data[i], 0U, &size, e)) return false;
        if (size > a->limits.max_generated_nodes - total)
            return fail(e, NLISP_UNKNOWN, forms.data[i]->span, "Unknown: expanded program node limit (%zu) exceeded", a->limits.max_generated_nodes);
        total += size;
    }
    return true;
}

static bool raw_tree_size(Arena *a, SExpr *x, size_t depth, size_t *result, Error *e) {
    size_t size = 1U, height = 1U, i;
    if (depth >= a->limits.max_expansion_depth)
        return fail(e, NLISP_UNKNOWN, x->span, "Unknown: process evidence depth limit (%zu) exceeded", a->limits.max_expansion_depth);
    if (x->raw_size != 0U) {
        if (x->raw_height > a->limits.max_expansion_depth - depth)
            return fail(e, NLISP_UNKNOWN, x->span, "Unknown: process evidence depth limit (%zu) exceeded", a->limits.max_expansion_depth);
        *result = x->raw_size; return true;
    }
    if (x->kind == SX_LIST) for (i = 0U; i < x->count; i++) {
        size_t child;
        if (!raw_tree_size(a, x->items[i], depth + 1U, &child, e)) return false;
        if (child > a->limits.max_generated_nodes || size > a->limits.max_generated_nodes - child)
            return fail(e, NLISP_UNKNOWN, x->span, "Unknown: process evidence node limit (%zu) exceeded", a->limits.max_generated_nodes);
        size += child;
        if (x->items[i]->raw_height + 1U > height) height = x->items[i]->raw_height + 1U;
    }
    x->raw_size = size; x->raw_height = height; *result = size; return true;
}

static bool process_evidence_size(Arena *a, Error *e) {
    size_t total = 0U, i;
    MacroTrace *trace;
    if (!a->capture_trace) return true;
    for (i = 0U; i < a->source_count + a->normalized_count; i++) {
        SExpr *x = i < a->source_count ? a->source_forms[i] : a->normalized_forms[i - a->source_count];
        size_t size;
        if (!raw_tree_size(a, x, 0U, &size, e)) return false;
        if (size > a->limits.max_generated_nodes - total)
            return fail(e, NLISP_UNKNOWN, x->span, "Unknown: process evidence node limit (%zu) exceeded", a->limits.max_generated_nodes);
        total += size;
    }
    for (trace = a->trace_head; trace != NULL; trace = trace->next) {
        SExpr *trees[3] = {(SExpr *)trace->input, trace->substitution, trace->definition->rule};
        size_t j, size;
        for (j = 0U; j < 4U; j++) {
            if (j == 3U) {
                if (!expanded_size(a, trace->substitution, 0U, &size, e)) return false;
            } else if (!raw_tree_size(a, trees[j], 0U, &size, e)) return false;
            if (size > a->limits.max_generated_nodes - total)
                return fail(e, NLISP_UNKNOWN, trace->input->span, "Unknown: process evidence node limit (%zu) exceeded", a->limits.max_generated_nodes);
            total += size;
        }
    }
    return true;
}

NLispLimits nlisp_default_limits(void) {
    NLispLimits limits = {10000U, 100000U, 128U, 1000000U}; return limits;
}

static NLispStatus nlisp_process_file_inner(const char *path, NLispCommand mode, const NLispLimits *limits,
                                            FILE *out, FILE *err) {
    Arena a = {0}; Error e = {false, NLISP_OK, {0U, 0U}, {0}};
    char *source; size_t len = 0U; Tokens ts = {NULL, 0U}; Forms forms = {NULL, 0U};
    Program p = {NULL, 0U}; Value *result = NULL;
    if (mode != NLISP_CHECK && mode != NLISP_RUN && mode != NLISP_EXPAND && mode != NLISP_EXPORT && mode != NLISP_SYNTAX) {
        fputs("invalid NLisp command\n", err); return NLISP_USAGE_ERROR;
    }
    a.capture_trace = mode == NLISP_EXPORT || mode == NLISP_SYNTAX;
    a.limits = limits == NULL ? nlisp_default_limits() : *limits;
    if (a.limits.max_expansion_depth > 512U) {
        fputs("max-expansion-depth must not exceed the native stack safety ceiling of 512\n", err);
        return NLISP_USAGE_ERROR;
    }
    source = read_source(path, &len, &e);
    if (source != NULL && lex(&a, source, len, &ts, &e) && parse_forms(&a, ts, &forms, &e) && remember_forms(&a, forms, false) &&
        flatten_defrec(&a, &forms, &e) && remember_forms(&a, forms, true) && collect_macros(&a, &forms, &e) &&
        parse_program(&a, forms, &p, &e) &&
        (mode == NLISP_SYNTAX || (check_program(&a, &p, &e) && check_program(&a, &p, &e))) && expanded_program_size(&a, forms, &e) && process_evidence_size(&a, &e)) {
        if (mode == NLISP_SYNTAX) {
            fputs("{\"format\":\"nlisp-syntax-v1\",\"source_text\":", out);
            print_json_string(out, source); fputs(",\"source_ast\":", out);
            print_raw_forms(out, a.source_forms, a.source_count);
            fputs(",\"normalized_ast\":", out);
            print_raw_forms(out, a.normalized_forms, a.normalized_count);
            fputc(',', out); print_export_limits(out, &a); fputs("}\n", out);
        } else if (mode == NLISP_RUN) {
            result = run_program(&a, &p, &e);
            if (result != NULL) { print_value(out, result); fputc('\n', out); }
        } else if (mode == NLISP_EXPORT) {
            size_t i;
            fputs("{\"format\":\"nlisp-scoped-expansion-v2\",\"source_text\":", out);
            print_json_string(out, source); fputs(",\"declarations\":[", out);
            for (i = 0U; i < forms.count; i++) {
                if (i != 0U) fputc(',', out);
                print_core_json(out, forms.data[i]);
            }
            fputc(']', out); print_process_evidence(out, &a); print_name_observations(out, &a); fputs("}\n", out);
        } else if (mode == NLISP_EXPAND) {
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

NLispStatus nlisp_process_file(const char *path, NLispCommand mode, const NLispLimits *limits,
                               FILE *out, FILE *err) {
    fenv_t caller_environment;
    NLispStatus status;
    if (feholdexcept(&caller_environment) != 0) {
        fputs("unable to isolate floating-point environment\n", err);
        return NLISP_RUNTIME_ERROR;
    }
    if (fesetround(FE_TONEAREST) != 0) {
        (void)fesetenv(&caller_environment);
        fputs("unable to select IEEE roundTiesToEven mode\n", err);
        return NLISP_RUNTIME_ERROR;
    }
    status = nlisp_process_file_inner(path, mode, limits, out, err);
    if (fesetenv(&caller_environment) != 0) {
        fputs("unable to restore caller floating-point environment\n", err);
        if (status == NLISP_OK) status = NLISP_RUNTIME_ERROR;
    }
    return status;
}

NLispStatus nlisp_check_file(const char *path, FILE *out, FILE *err) {
    return nlisp_process_file(path, NLISP_CHECK, NULL, out, err);
}
NLispStatus nlisp_run_file(const char *path, FILE *out, FILE *err) {
    return nlisp_process_file(path, NLISP_RUN, NULL, out, err);
}

NLispStatus nlisp_expand_file(const char *path, FILE *out, FILE *err) {
    return nlisp_process_file(path, NLISP_EXPAND, NULL, out, err);
}

NLispStatus nlisp_export_file(const char *path, FILE *out, FILE *err) {
    return nlisp_process_file(path, NLISP_EXPORT, NULL, out, err);
}
