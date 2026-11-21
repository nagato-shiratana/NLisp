#!/usr/bin/env python3
"""Export scoped C expansion into a Lean-checked core or polymorphic IR.

The bridge is untrusted: Lean independently checks the emitted closed term.
Unsupported features fail explicitly; no expression is evaluated away.
"""
import argparse
import base64
import hashlib
import json
import os
import pathlib
import re
import subprocess
import struct
import sys
import tempfile


def canonical_json(value):
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(',', ':'))


def digest(data):
    return hashlib.sha256(data).hexdigest()


class UnknownResult(Exception):
    """A resource limit was reached; neither invalidity nor divergence is proved."""


def read_bounded(stream, limit, description):
    if limit < 0:
        raise ValueError('resource limits must be nonnegative')
    chunks, size = [], 0
    while True:
        chunk = stream.read(min(65536, limit - size + 1))
        if not chunk:
            return b''.join(chunks)
        size += len(chunk)
        if size > limit:
            raise UnknownResult(f'{description} limit ({limit} bytes) exceeded')
        chunks.append(chunk)


def read_bounded_file(path, limit):
    with path.open('rb') as stream:
        return read_bounded(stream, limit, 'input file size')


def run_export(command, max_output_bytes):
    """Bound captured process evidence even when shared literals expand hugely."""
    process = None
    with tempfile.TemporaryFile() as errors:
        try:
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=errors)
            output = read_bounded(process.stdout, max_output_bytes, 'process evidence output')
            process.wait()
            errors.seek(0)
            diagnostics = errors.read(8192).decode('utf-8', errors='replace')
            return subprocess.CompletedProcess(command, process.returncode, output.decode('utf-8'), diagnostics)
        finally:
            if process is not None:
                if process.poll() is None:
                    process.kill()
                process.wait()
                process.stdout.close()


def run_lean_command(command):
    root = pathlib.Path(__file__).resolve().parents[1]
    result = subprocess.run(command, cwd=root, capture_output=True, encoding='utf-8')
    if result.returncode:
        if result.returncode < 0 or result.returncode in (134, 137, 139, 143):
            raise UnknownResult(f'Lean process terminated abnormally (status {result.returncode})')
        diagnostics = result.stdout + result.stderr
        if any(marker in diagnostics.lower() for marker in (
            'maximum recursion depth', 'maximum number of heartbeats',
            'out of memory', 'stack overflow', 'deep recursion was detected',
        )):
            raise UnknownResult('Lean resource limit: ' + diagnostics[:2000])
        raise subprocess.CalledProcessError(result.returncode, command,
                                            output=result.stdout, stderr=result.stderr)
    return result


STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def generated_theorems(text):
    namespaces, names = [], []
    for line in text.split('\n'):
        opened = re.fullmatch(r'namespace ([A-Za-z_][A-Za-z0-9_.]*)', line.strip())
        closed = re.fullmatch(r'end(?: [A-Za-z_][A-Za-z0-9_.]*)?', line.strip())
        theorem = re.match(r'^theorem ([A-Za-z_][A-Za-z0-9_]*)\b', line)
        if opened:
            namespaces.append(opened[1])
        elif closed and namespaces:
            namespaces.pop()
        elif theorem:
            names.append('.'.join([*namespaces, theorem[1]]))
    return names


def check_generated_axioms(output, names):
    checked = {}
    for line in output.splitlines():
        match = re.fullmatch(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", line)
        if match:
            dependencies = set(match[3].split(', ')) if match[3] else set()
            checked[match[1]] = dependencies
    for name in names:
        if name not in checked:
            raise ValueError('Lean did not report an axiom audit for ' + name)
        if not checked[name] <= STANDARD_AXIOMS:
            raise ValueError('certificate depends on unsupported axioms: ' + name + ': ' +
                             ', '.join(sorted(checked[name] - STANDARD_AXIOMS)))


def verify_certificate(certificate, output, lake, publish=True):
    """Build the pinned models, check Lean, then atomically publish the artifact."""
    root = pathlib.Path(__file__).resolve().parents[1]
    if os.path.sep in lake:
        lake = str(pathlib.Path(lake).resolve())
    snapshot = environment_hashes()
    names = generated_theorems(certificate)
    if certificate.startswith(BUNDLE_HEADER):
        manifest, _ = unpack_bundle(certificate)
        if manifest['environment'] != snapshot:
            raise ValueError('Lean environment changed before certificate verification')
        primary = ('VerifiedNLispSource.source_rules_wellFounded' if manifest['conversion']['mode'] == 'termination'
                   else 'VerifiedNLispSource.source_expands_with_scopes')
        if primary not in names:
            raise ValueError('certificate lacks the source correspondence theorem')
    run_lean_command([lake, 'build'])
    pinned = (root / 'lean-toolchain').read_text().strip()
    match = re.fullmatch(r'leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)', pinned)
    if match is None:
        raise ValueError('unsupported Lean toolchain specification')
    version = run_lean_command([lake, 'env', 'lean', '--version']).stdout
    if not version.startswith('Lean (version ' + match[1] + ','):
        raise ValueError('actual Lean version differs from lean-toolchain')
    if snapshot != environment_hashes():
        raise ValueError('Lean model files changed during the build')
    staged = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', newline='', suffix='.lean',
                                         prefix='NlispCertificate_', dir=output.parent if publish else None,
                                         delete=False) as stream:
            staged = pathlib.Path(stream.name).resolve()
            stream.write(certificate)
            stream.write('\n' + ''.join('#print axioms ' + name + '\n' for name in names))
        result = run_lean_command([lake, 'env', 'lean', str(staged)])
        check_generated_axioms(result.stdout, names)
        if snapshot != environment_hashes():
            raise ValueError('Lean model files changed during certificate verification')
        if publish:
            # Audit commands are verifier-local; publish the exact hashed artifact.
            with staged.open('w', encoding='utf-8', newline='') as stream:
                stream.write(certificate)
            os.replace(staged, output)
            staged = None
    finally:
        if staged is not None:
            staged.unlink(missing_ok=True)


def atom(node):
    return node['atom'] if isinstance(node, dict) else None


def parse_type(node, variables=None):
    name = atom(node)
    if variables and name in variables:
        return variables[name]
    if name in ('Integer', 'Boolean', 'Unit', 'Float', 'String', 'Character'):
        return name
    if isinstance(node, list) and atom(node[0]) in ('List', 'Option'):
        return atom(node[0]), parse_type(node[1], variables)
    if isinstance(node, list) and atom(node[0]) == 'Function':
        return 'Function', tuple(parse_type(t, variables) for t in node[1]), parse_type(node[2], variables)
    raise ValueError(f'type outside Lean core: {node}')


def substitute_type(ty, substitutions):
    if isinstance(ty, str):
        return ty
    if ty[0] == 'Variable':
        return substitutions[ty[1]]
    if ty[0] in ('List', 'Option'):
        return ty[0], substitute_type(ty[1], substitutions)
    return 'Function', tuple(substitute_type(t, substitutions) for t in ty[1]), substitute_type(ty[2], substitutions)


def match_type(pattern, actual, substitutions):
    if isinstance(pattern, tuple) and pattern[0] == 'Variable':
        name = pattern[1]
        if name in substitutions and substitutions[name] != actual:
            raise ValueError(f'inconsistent type argument for {name}')
        substitutions[name] = actual
    elif isinstance(pattern, str):
        if pattern != actual:
            raise ValueError('type argument mismatch')
    elif not isinstance(actual, tuple) or pattern[0] != actual[0]:
        raise ValueError('type constructor mismatch')
    elif pattern[0] in ('List', 'Option'):
        match_type(pattern[1], actual[1], substitutions)
    else:
        if len(pattern[1]) != len(actual[1]):
            raise ValueError('function arity mismatch')
        for p, a in zip(pattern[1], actual[1]):
            match_type(p, a, substitutions)
        match_type(pattern[2], actual[2], substitutions)


def lean_type(ty):
    if isinstance(ty, str):
        return {'Integer': 'Ty.integer', 'Boolean': 'Ty.boolean', 'Unit': 'Ty.unit',
                'Float': 'Ty.floating', 'String': 'Ty.string', 'Character': 'Ty.character'}[ty]
    if ty[0] in ('List', 'Option'):
        return f'(Ty.{ty[0].lower()} {lean_type(ty[1])})'
    result = lean_type(ty[2])
    for arg in reversed(ty[1] or ('Unit',)):
        result = f'(Ty.fn {lean_type(arg)} {result})'
    return result


def var(index):
    result = 'Var.zero'
    for _ in range(index):
        result = f'(Var.succ {result})'
    return f'(Expr.var {result})'


def lam(ty, body):
    return f'(Expr.lam (a := {lean_type(ty)}) {body})'


def app(fn, arg):
    return f'(Expr.app {fn} {arg})'


class Exporter:
    def __init__(self, document, max_certificate_bytes=4194304, max_conversion_steps=100000, record_process=False):
        if document.get('format') not in ('nlisp-scoped-expansion-v1', 'nlisp-scoped-expansion-v2'):
            raise ValueError('unsupported scoped expansion format')
        self.max_certificate_bytes = max_certificate_bytes
        self.max_conversion_steps = max_conversion_steps
        self.conversion_steps = 0
        self.record_process = record_process
        self.process = []
        self.process_bytes = 0
        self.globals = {}
        self.schemes = {}
        self.type_variables = {}
        self.active = set()
        for index, decl in enumerate(document['declarations']):
            name = atom(decl[0])
            if name == 'define':
                self.globals[atom(decl[1][0])] = (index, parse_type(decl[1][1]), decl[2], None)
            elif name == 'defun' and len(decl) == 5:
                params = [(atom(p[0]), parse_type(p[1])) for p in decl[2]]
                ty = 'Function', tuple(t for _, t in params), parse_type(decl[3])
                self.globals[atom(decl[1])] = (index, ty, decl[4], params)
            elif name == 'defun' and len(decl) == 4 and atom(decl[2][0]) == 'forall':
                signature = decl[2]
                variables = [atom(v) for v in signature[1]]
                bindings = {v: ('Variable', v) for v in variables}
                params = [(atom(p[0]), parse_type(p[1], bindings)) for p in signature[2]]
                ty = 'Function', tuple(t for _, t in params), parse_type(signature[3], bindings)
                self.globals[atom(decl[1])] = (index, ty, decl[3], params)
                self.schemes[atom(decl[1])] = variables
            else:
                raise ValueError('unsupported declaration')

    def parse_type(self, node):
        return parse_type(node, self.type_variables)

    def is_scheme(self, node, ctx):
        name = atom(node)
        return name in self.schemes and not (
            node['origin'] is None and any(local == name for local, _ in ctx))

    def resolve(self, node, ctx, substitutions=None):
        name, origin = atom(node), node['origin']
        scheme = self.is_scheme(node, ctx)
        concrete_type = self.globals[name][1] if name in self.globals else None
        if scheme:
            if substitutions is None:
                raise ValueError(f'polymorphic value {name} needs type-app or call arguments')
            concrete_type = substitute_type(concrete_type, substitutions)
        for index, (local, ty) in enumerate(ctx):
            if (origin is None and name == local) or local == ('function', name, concrete_type):
                return var(index), ty
            if local == ('global', name):
                declaration_index = self.globals[name][0]
                if origin is None or declaration_index < origin:
                    return var(index), ty
        if name in self.globals:
            index, ty, body, params = self.globals[name]
            if scheme:
                ty = concrete_type
                params = [(n, substitute_type(t, substitutions)) for n, t in params]
            if origin is not None and params is None and index >= origin:
                raise ValueError(f'definition-site scope does not contain {name}')
            key = (name, ty)
            if len(self.active) > 100:
                raise UnknownResult('recursive specialization/dependency limit (100) reached')
            if key in self.active:
                raise ValueError(f'cyclic global initializer or unresolved recursion for {name}')
            self.active.add(key)
            old_variables = self.type_variables
            self.type_variables = substitutions or {}
            try:
                # Keep context indices, but hide caller names from global definitions.
                hidden = [(n if isinstance(n, tuple) else None, t) for n, t in ctx]
                if params is None:
                    term, actual = self.expr(body, hidden)
                else:
                    term, actual = self.function(params, body, [(('function', name, ty), ty)] + hidden)
                    term = f'(Expr.fix {term})'
                if actual != ty:
                    raise ValueError(f'global type mismatch for {name}')
                return term, ty
            finally:
                self.type_variables = old_variables
                self.active.remove(key)
        if name in ('+', '-', '*', '<=', 'integer='):
            result = 'Integer' if name in ('+', '-', '*') else 'Boolean'
            operation = {'+': 'add', '-': 'sub', '*': 'mul', '<=': 'leq', 'integer=': 'eqInt'}[name]
            term = f'(Expr.{operation} {var(1)} {var(0)})'
            return lam('Integer', lam('Integer', term)), ('Function', ('Integer', 'Integer'), result)
        raise ValueError(f'identifier or builtin outside Lean core: {name}')

    def function(self, params, body, ctx):
        if not params:
            term, result = self.expr(body, [(None, 'Unit')] + ctx)
            return lam('Unit', term), ('Function', (), result)
        term, result = self.expr(body, list(reversed(params)) + ctx)
        for _, ty in reversed(params):
            term = self.check_term(lam(ty, term))
        return term, ('Function', tuple(t for _, t in params), result)

    def check_term(self, term):
        if self.conversion_steps >= self.max_conversion_steps:
            raise UnknownResult(f'certificate conversion work limit ({self.max_conversion_steps}) exceeded')
        self.conversion_steps += 1
        if len(term.encode('utf-8')) > self.max_certificate_bytes:
            raise UnknownResult(f'certificate size limit ({self.max_certificate_bytes} bytes) exceeded')
        return term

    def expr(self, node, ctx):
        # Check on entry as well, so a recursive descent cannot consume an
        # unbounded amount of work before it begins returning terms.
        self.check_term('')
        term, ty = self.expr_inner(node, ctx)
        if self.record_process:
            event = {'stage': 'elaboration', 'input': node,
                     'context': [{'binding': n, 'type': t} for n, t in ctx],
                     'term': term, 'type': ty}
            self.record_event(event)
        return self.check_term(term), ty

    def record_event(self, event):
        cost = len(canonical_json(event).encode('utf-8'))
        if cost > self.max_certificate_bytes - self.process_bytes:
            raise UnknownResult('conversion process evidence size limit exceeded')
        self.process_bytes += cost
        self.process.append(event)

    def expr_inner(self, node, ctx):
        name = atom(node)
        if name is not None:
            if name in ('true', 'false'):
                return f'(Expr.bool {name})', 'Boolean'
            if name == 'unit':
                return 'Expr.unit', 'Unit'
            if re.fullmatch(r'-?(0|[1-9][0-9]*)', name):
                return f'(Expr.int ({name}))', 'Integer'
            return self.resolve(node, ctx)
        tag = atom(node[0])
        if tag == 'type-app':
            name = atom(node[1])
            if not self.is_scheme(node[1], ctx):
                raise ValueError('type-app requires a global polymorphic function')
            arguments = [self.parse_type(t) for t in node[2:]]
            if len(arguments) != len(self.schemes[name]):
                raise ValueError('explicit type arity mismatch')
            return self.resolve(node[1], ctx, dict(zip(self.schemes[name], arguments)))
        if tag == 'lambda':
            params = [(atom(p[0]), self.parse_type(p[1])) for p in node[1]]
            term, ty = self.function(params, node[3], ctx)
            if ty[2] != self.parse_type(node[2]):
                raise ValueError('lambda return type mismatch')
            return term, ty
        if tag == 'if':
            condition, ct = self.expr(node[1], ctx)
            yes, yt = self.expr(node[2], ctx)
            no, nt = self.expr(node[3], ctx)
            if ct != 'Boolean' or yt != nt:
                raise ValueError('ill-typed conditional')
            return f'(Expr.ite {condition} {yes} {no})', yt
        if tag == 'let':
            params = [(atom(b[0][0]), self.parse_type(b[0][1])) for b in node[1]]
            term, ty = self.function(params, node[2], ctx)
            if not params:
                return app(term, 'Expr.unit'), ty[2]
            for binding, (_, expected) in zip(node[1], params):
                value, actual = self.expr(binding[1], ctx)
                if actual != expected:
                    raise ValueError('let binding type mismatch')
                term = app(term, value)
            return term, ty[2]
        if tag == 'begin':
            # Sequence through strict applications, retaining all expressions.
            if len(node) == 2:
                return self.expr(node[1], ctx)
            first, ft = self.expr(node[1], ctx)
            rest, rt = self.expr([node[0]] + node[2:], [(None, ft)] + ctx)
            return app(lam(ft, rest), first), rt
        if tag in ('Nil', 'None'):
            ty = self.parse_type(node[1])
            constructor = 'nil' if tag == 'Nil' else 'none'
            return f'(Expr.{constructor} (a := {lean_type(ty)}))', ('List' if tag == 'Nil' else 'Option', ty)
        if tag in ('Cons', 'Some'):
            ty = self.parse_type(node[1])
            head, ht = self.expr(node[2], ctx)
            if ht != ty:
                raise ValueError('constructor type mismatch')
            if tag == 'Some':
                return f'(Expr.some {head})', ('Option', ty)
            tail, tt = self.expr(node[3], ctx)
            if tt != ('List', ty):
                raise ValueError('Cons tail type mismatch')
            return f'(Expr.cons {head} {tail})', tt
        if tag == 'match':
            scrutinee, st = self.expr(node[1], ctx)
            if not isinstance(st, tuple) or st[0] not in ('List', 'Option'):
                raise ValueError('invalid match scrutinee')
            clauses = {atom(c[0][0]): c for c in node[2:]}
            if st[0] == 'List':
                empty, full, op = clauses['Nil'], clauses['Cons'], 'matchList'
                local = [(atom(full[0][1]), st[1]), (atom(full[0][2]), st)] + ctx
            else:
                empty, full, op = clauses['None'], clauses['Some'], 'matchOption'
                local = [(atom(full[0][1]), st[1])] + ctx
            e, et = self.expr(empty[1], ctx)
            f, ft = self.expr(full[1], local)
            if et != ft:
                raise ValueError('match result type mismatch')
            return f'(Expr.{op} {scrutinee} {e} {f})', et
        compiled_arguments = [self.expr(argument, ctx) for argument in node[1:]]
        if self.is_scheme(node[0], ctx):
            name = atom(node[0])
            pattern = self.globals[name][1]
            substitutions = {}
            if len(pattern[1]) != len(compiled_arguments):
                raise ValueError('polymorphic call arity mismatch')
            for expected, (_, actual) in zip(pattern[1], compiled_arguments):
                match_type(expected, actual, substitutions)
            if set(substitutions) != set(self.schemes[name]):
                raise ValueError('type arguments cannot be inferred from call arguments')
            fn, ft = self.resolve(node[0], ctx, substitutions)
        else:
            fn, ft = self.expr(node[0], ctx)
        if not isinstance(ft, tuple) or ft[0] != 'Function' or len(ft[1]) != len(node) - 1:
            raise ValueError('invalid function application')
        if not ft[1]:
            return app(fn, 'Expr.unit'), ft[2]
        for (value, actual), expected in zip(compiled_arguments, ft[1]):
            if actual != expected:
                raise ValueError('function argument type mismatch')
            fn = app(fn, value)
        return fn, ft[2]

    def closed_term(self):
        _, ty, body, params = self.globals['main']
        if ty != ('Function', (), 'Integer') or params != []:
            raise ValueError('expected main : () -> Integer')
        values = [(name, data) for name, data in self.globals.items() if data[3] is None]

        def initialize(index, ctx):
            if index == len(values):
                return self.expr(body, ctx)
            name, (_, ty, initializer, _) = values[index]
            value, actual = self.expr(initializer, ctx)
            if actual != ty:
                raise ValueError(f'initializer type mismatch for {name}')
            rest, rt = initialize(index + 1, [(('global', name), ty)] + ctx)
            return self.check_term(app(lam(ty, rest), value)), rt

        term, actual = initialize(0, [])
        if actual != 'Integer':
            raise ValueError('invalid main result')
        if self.record_process:
            self.record_event({'stage': 'closed_program', 'term': term, 'type': actual,
                               'globals': [{'name': name, 'index': data[0], 'type': data[1]}
                                           for name, data in self.globals.items()]})
        return term

    def export(self):
        term = self.closed_term()
        if any(t in term for t in ('Ty.floating', 'Ty.string', 'Ty.character')):
            raise ValueError('type outside operational Lean core')
        return ('import NLisp\nopen NLisp\n\n'
                f'def expandedProgram : Expr [] Ty.integer :=\n  {term}\n\n'
                'theorem expandedProgram_notStuck :\n'
                '    Value expandedProgram ∨ ∃ next, Step expandedProgram next :=\n'
                '  notStuck expandedProgram\n')


# Name, certificate constructor, input type, result type, arity.
PRIMITIVES = [
    ('+', 'add', 'Integer', 'Integer', 2), ('-', 'sub', 'Integer', 'Integer', 2),
    ('*', 'mul', 'Integer', 'Integer', 2),
    ('quotient', 'quotient', 'Integer', ('Option', 'Integer'), 2),
    ('remainder', 'remainder', 'Integer', ('Option', 'Integer'), 2),
    ('<', 'lt', 'Integer', 'Boolean', 2), ('<=', 'le', 'Integer', 'Boolean', 2),
    ('>', 'gt', 'Integer', 'Boolean', 2), ('>=', 'ge', 'Integer', 'Boolean', 2),
    ('integer=', 'intEq', 'Integer', 'Boolean', 2),
    ('float+', 'fadd', 'Float', 'Float', 2), ('float-', 'fsub', 'Float', 'Float', 2),
    ('float*', 'fmul', 'Float', 'Float', 2), ('float/', 'fdiv', 'Float', 'Float', 2),
    ('float<', 'flt', 'Float', 'Boolean', 2), ('float<=', 'fle', 'Float', 'Boolean', 2),
    ('float>', 'fgt', 'Float', 'Boolean', 2), ('float>=', 'fge', 'Float', 'Boolean', 2),
    ('float=', 'floatEq', 'Float', 'Boolean', 2),
    ('boolean=', 'boolEq', 'Boolean', 'Boolean', 2), ('not', 'not', 'Boolean', 'Boolean', 1),
    ('string=', 'stringEq', 'String', 'Boolean', 2),
    ('character=', 'charEq', 'Character', 'Boolean', 2),
    ('string-append', 'append', 'String', 'String', 2),
    ('to-float', 'toFloat', 'Integer', 'Float', 1),
    ('float-truncate', 'truncate', 'Float', ('Option', 'Integer'), 1),
]


def unicode_scalar(value):
    if value < 0 or value > 0x10ffff or 0xd800 <= value <= 0xdfff:
        raise ValueError('invalid Unicode scalar value')
    return chr(value)


def decode_string(token):
    if len(token) < 2 or token[0] != '"' or token[-1] != '"':
        raise ValueError('invalid string token')
    text = token[1:-1]
    result = []
    index = 0
    escapes = {'n': '\n', 'r': '\r', 't': '\t', '"': '"', '\\': '\\'}
    while index < len(text):
        if text[index] != '\\':
            result.append(unicode_scalar(ord(text[index])))
            index += 1
            continue
        index += 1
        if index >= len(text):
            raise ValueError('truncated string escape')
        if text[index] in escapes:
            result.append(escapes[text[index]])
            index += 1
            continue
        match = re.match(r'u\{([0-9a-fA-F]{1,6})\}', text[index:])
        if match is None:
            raise ValueError('invalid Unicode string escape')
        result.append(unicode_scalar(int(match[1], 16)))
        index += len(match[0])
    return ''.join(result)


class TypeExporter(Exporter):
    """Typing derivations for every builtin, without operational claims."""
    def resolve(self, node, ctx, substitutions=None):
        name = atom(node)
        shadowed = node['origin'] is None and any(local == name for local, _ in ctx)
        if not shadowed and name not in self.globals:
            for source, primitive, input_type, output_type, arity in PRIMITIVES:
                if name == source:
                    return f'(Expr.builtin Primitive.{primitive})', ('Function', (input_type,) * arity, output_type)
        return super().resolve(node, ctx, substitutions)

    def expr_inner(self, node, ctx):
        token = atom(node)
        if token is not None:
            if token.startswith('"'):
                characters = ', '.join(f'(Char.ofNat {ord(c)})' for c in decode_string(token))
                return f'(Expr.str (String.mk [{characters}]))', 'String'
            if token.startswith('#\\'):
                value = token[2:]
                if value in ('newline', 'space', 'tab'):
                    value = {'newline': '\n', 'space': ' ', 'tab': '\t'}[value]
                elif re.fullmatch(r'u\{[0-9a-fA-F]{1,6}\}', value):
                    value = unicode_scalar(int(value[2:-1], 16))
                if len(value) != 1:
                    raise ValueError('invalid character token')
                unicode_scalar(ord(value))
                return f'(Expr.char (Char.ofNat {ord(value)}))', 'Character'
            if re.fullmatch(r'-?[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?', token):
                bits = struct.unpack('>Q', struct.pack('>d', float(token)))[0]
                return f'(Expr.floatBits (UInt64.ofNat {bits}))', 'Float'
        return super().expr_inner(node, ctx)

    def export(self):
        term = self.closed_term()
        return ('import NLisp\nopen NLisp.TypedExpansion\n\n'
                f'def expandedProgram : Expr [] Ty.integer :=\n  {term}\n\n'
                'theorem expandedProgram_wellTyped :\n'
                '    HasType [] expandedProgram.erase Ty.integer :=\n'
                '  expandedProgram.hasType\n')


class PolyExporter(Exporter):
    """Lower generic functions once; Lean checks the resulting polymorphic IR.

    This path deliberately rejects top-level values and types outside Surface.
    It does not assert a proved correspondence between this Python lowering and
    the independently checked scoped syntax. That connection is a separate duty.
    """
    def __init__(self, document, **options):
        super().__init__(document, **options)
        if any(data[3] is None for data in self.globals.values()):
            raise ValueError('poly mode requires explicit function parameters for top-level captures')
        self.indices = {name: index for index, name in enumerate(self.globals)}
        self.variable_indices = {}
        self.global_ids = {atom(d[1]): d[1]['token_identity'] for d in document['declarations']}
        self.parameter_nodes = {atom(d[1]): d[2] if len(d) == 5 else d[2][2]
                                for d in document['declarations']}

    @staticmethod
    def binding(node, ty):
        return ('binding', natural(node['token_identity'], 'binder identity'), atom(node)), ty

    def is_scheme(self, node, ctx):
        name = atom(node)
        return name in self.schemes and node['resolved_identity'] == self.global_ids[name]

    def ty(self, ty):
        if isinstance(ty, str):
            if ty not in ('Integer', 'Boolean', 'Unit'):
                raise ValueError('type outside polymorphic operational model: ' + ty)
            return {'Integer': 'Ty.integer', 'Boolean': 'Ty.boolean', 'Unit': 'Ty.unit'}[ty]
        if ty[0] == 'Variable':
            return f'(Ty.var {self.variable_indices[ty[1]]})'
        if ty[0] in ('List', 'Option'):
            return f'(Ty.{ty[0].lower()} {self.ty(ty[1])})'
        return f'(Ty.fn [{", ".join(self.ty(t) for t in ty[1])}] {self.ty(ty[2])})'

    def resolve(self, node, ctx, substitutions=None):
        name = atom(node)
        selected = node['resolved_identity']
        for index, (local, ty) in enumerate(ctx):
            if local[1] == selected:
                return f'(Expr.var {index})', ty
        if name in self.globals and selected == self.global_ids[name]:
            _, ty, _, _ = self.globals[name]
            variables = self.schemes.get(name, [])
            if variables and substitutions is None:
                raise ValueError('polymorphic value needs explicit or inferred type arguments')
            arguments = [substitutions[v] for v in variables]
            actual = substitute_type(ty, substitutions) if variables else ty
            return f'(Expr.global {self.indices[name]} [{", ".join(self.ty(t) for t in arguments)}])', actual
        operations = {'+': 'add', '-': 'sub', '*': 'mul', '<=': 'le', 'integer=': 'intEq'}
        builtin_ids = {'+': 3, '-': 6, '*': 9, '<=': 15, 'integer=': 24}
        if name in operations and selected == builtin_ids[name]:
            result = 'Integer' if name in ('+', '-', '*') else 'Boolean'
            body = f'(Expr.{operations[name]} (Expr.var 0) (Expr.var 1))'
            return (f'(Expr.lam [Ty.integer, Ty.integer] {self.ty(result)} {body})',
                    ('Function', ('Integer', 'Integer'), result))
        raise ValueError('identifier outside polymorphic operational model: ' + str(name))

    def expr_inner(self, node, ctx):
        token = atom(node)
        if token is not None:
            if token in ('true', 'false'):
                return f'(Expr.bool {token})', 'Boolean'
            if token == 'unit':
                return 'Expr.unit', 'Unit'
            if re.fullmatch(r'-?(0|[1-9][0-9]*)', token):
                return f'(Expr.int ({token}))', 'Integer'
            return self.resolve(node, ctx)
        tag = atom(node[0])
        if tag == 'type-app':
            name = atom(node[1])
            if not self.is_scheme(node[1], ctx):
                raise ValueError('type-app requires a global polymorphic function')
            arguments = [self.parse_type(t) for t in node[2:]]
            if len(arguments) != len(self.schemes[name]):
                raise ValueError('explicit type arity mismatch')
            return self.resolve(node[1], ctx, dict(zip(self.schemes[name], arguments)))
        if tag == 'lambda':
            parameters = [self.binding(p[0], self.parse_type(p[1])) for p in node[1]]
            result = self.parse_type(node[2])
            body, actual = self.expr(node[3], parameters + ctx)
            if actual != result:
                raise ValueError('lambda result mismatch')
            return (f'(Expr.lam [{", ".join(self.ty(t) for _, t in parameters)}] {self.ty(result)} {body})',
                    ('Function', tuple(t for _, t in parameters), result))
        if tag == 'if':
            c, ct = self.expr(node[1], ctx)
            y, yt = self.expr(node[2], ctx)
            n, nt = self.expr(node[3], ctx)
            if ct != 'Boolean' or yt != nt:
                raise ValueError('conditional type mismatch')
            return f'(Expr.ite {c} {y} {n})', yt
        if tag == 'let':
            parameters = [self.binding(b[0][0], self.parse_type(b[0][1])) for b in node[1]]
            values = [self.expr(b[1], ctx) for b in node[1]]
            if [t for _, t in values] != [t for _, t in parameters]:
                raise ValueError('parallel let type mismatch')
            body, result = self.expr(node[2], parameters + ctx)
            return (f'(Expr.letMany [{", ".join(self.ty(t) for _, t in parameters)}] '
                    f'[{", ".join(v for v, _ in values)}] {body})', result)
        if tag == 'begin':
            if len(node) < 2:
                raise ValueError('begin must be nonempty')
            expressions = [self.expr(e, ctx) for e in node[1:]]
            return f'(Expr.begin {expressions[0][0]} [{", ".join(e for e, _ in expressions[1:])}])', expressions[-1][1]
        if tag in ('Nil', 'None'):
            ty = self.parse_type(node[1])
            return f'(Expr.{tag.lower()} {self.ty(ty)})', ('List' if tag == 'Nil' else 'Option', ty)
        if tag in ('Cons', 'Some'):
            ty = self.parse_type(node[1])
            head, ht = self.expr(node[2], ctx)
            if ht != ty:
                raise ValueError('constructor type mismatch')
            if tag == 'Some':
                return f'(Expr.some {self.ty(ty)} {head})', ('Option', ty)
            tail, tt = self.expr(node[3], ctx)
            if tt != ('List', ty):
                raise ValueError('Cons tail type mismatch')
            return f'(Expr.cons {self.ty(ty)} {head} {tail})', tt
        if tag == 'match':
            target, tt = self.expr(node[1], ctx)
            if not isinstance(tt, tuple) or tt[0] not in ('List', 'Option'):
                raise ValueError('invalid match target')
            clauses = {atom(c[0][0]): c for c in node[2:]}
            if tt[0] == 'List':
                empty, full = clauses['Nil'], clauses['Cons']
                local = [self.binding(full[0][1], tt[1]), self.binding(full[0][2], tt)]
                operation = 'matchList'
            else:
                empty, full = clauses['None'], clauses['Some']
                local = [self.binding(full[0][1], tt[1])]
                operation = 'matchOption'
            e, et = self.expr(empty[1], ctx)
            f, ft = self.expr(full[1], local + ctx)
            if et != ft:
                raise ValueError('match result mismatch')
            return f'(Expr.{operation} {target} {e} {f})', et
        arguments = [self.expr(a, ctx) for a in node[1:]]
        if self.is_scheme(node[0], ctx):
            name = atom(node[0])
            pattern = self.globals[name][1]
            substitutions = {}
            if len(pattern[1]) != len(arguments):
                raise ValueError('polymorphic call arity mismatch')
            for expected, (_, actual) in zip(pattern[1], arguments):
                match_type(expected, actual, substitutions)
            if set(substitutions) != set(self.schemes[name]):
                raise ValueError('type arguments cannot be inferred from call arguments')
            function, ft = self.resolve(node[0], ctx, substitutions)
        else:
            function, ft = self.expr(node[0], ctx)
        if not isinstance(ft, tuple) or ft[0] != 'Function' or ft[1] != tuple(t for _, t in arguments):
            raise ValueError('function argument mismatch')
        return f'(Expr.app {function} [{", ".join(e for e, _ in arguments)}])', ft[2]

    def export(self):
        if 'main' not in self.globals or self.globals['main'][1] != ('Function', (), 'Integer'):
            raise ValueError('expected main : () -> Integer')
        signatures, bodies = [], []
        for name, (_, ty, body, parameters) in self.globals.items():
            variables = self.schemes.get(name, [])
            self.type_variables = {v: ('Variable', v) for v in variables}
            self.variable_indices = {v: i for i, v in enumerate(variables)}
            signatures.append(f'⟨{len(variables)}, [{", ".join(self.ty(t) for t in ty[1])}], {self.ty(ty[2])}⟩')
            context = [self.binding(p[0], ty) for p, (_, ty) in zip(self.parameter_nodes[name], parameters)]
            term, actual = self.expr(body, context)
            if actual != ty[2]:
                raise ValueError('function result mismatch: ' + name)
            bodies.append(term)
        self.record_event({'stage': 'generic_program', 'signatures': signatures, 'bodies': bodies})
        return ('import NLisp\nopen NLisp.Surface\nnamespace VerifiedPolyProgram\n'
                f'def signatures : List Signature := [{", ".join(signatures)}]\n'
                f'def bodies : List Expr := [{", ".join(bodies)}]\n'
                'def checked := elaborateProgram 512 signatures bodies\n'
                'theorem all_bodies_check : checked.isSome = true := by decide\n'
                'def program : NLisp.PolyIR.Program := checked.get all_bodies_check\n'
                'def source : Definitions := signatures.zip bodies\n'
                'theorem program_erasure : program.erase = NLisp.PolyIR.eraseDefinitions source := by rfl\n'
                f'def entry : Expr := .app (.global {self.indices["main"]} []) []\n'
                'theorem entry_checks : (elaborate 512 signatures 0 [] entry Ty.integer).isSome = true := by decide\n'
                'theorem execution_erases (fuel : Nat) :\n'
                '    NLisp.PolyIR.eraseResult (evaluate source fuel [] entry) =\n'
                '      NLisp.PolyIR.evaluate program.erase fuel [] (NLisp.PolyIR.erase entry) := by\n'
                '  rw [program_erasure]\n'
                '  exact (NLisp.PolyIR.execution_commutes source fuel).1 [] entry\n'
                'end VerifiedPolyProgram\n')


BUNDLE_HEADER = '-- NLisp process certificate v1; cryptographic signature: none\n'
BUNDLE_HASH = '-- NLISP-PAYLOAD-SHA256 '
BUNDLE_BEGIN = '-- BEGIN NLISP-CERTIFICATE-PAYLOAD\n'
BUNDLE_END = '-- END NLISP-CERTIFICATE-PAYLOAD\n'
ASSURANCE = {'process': 'deterministic replay',
             'kernel_checks': ['source parsing and defrec normalization',
                               'finite hygienic expansion derivation', 'scoped binding identities'],
             'formal_semantic_preservation': False,
             'cryptographic_signature': None}
TERMINATION_ASSURANCE = {
    'process': 'deterministic syntax replay',
    'kernel_checks': ['source parsing and defrec normalization',
                      'well-founded conservative macro call candidate graph'],
    'formal_semantic_preservation': False, 'cryptographic_signature': None,
}
POLY_ASSURANCE = {
    **ASSURANCE,
    'kernel_checks': [*ASSURANCE['kernel_checks'], 'generic body and integer entry typing',
                      'annotated source to IR structural correspondence',
                      'finite identity-based source evaluation preservation',
                      'polymorphic evaluator type preservation and exclusion of type errors'],
}


def assurance_for(mode):
    if mode == 'termination':
        return TERMINATION_ASSURANCE
    return POLY_ASSURANCE if mode == 'poly' else ASSURANCE


C_LIMITS = {'max_expansions': 10000, 'max_generated_nodes': 100000,
            'max_expansion_depth': 128, 'max_check_steps': 1000000}


def environment_hashes():
    root = pathlib.Path(__file__).resolve().parents[1]
    names = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'NLisp.lean']
    names.extend(path.relative_to(root).as_posix() for path in sorted((root / 'NLisp').rglob('*.lean')))
    return {name: digest((root / name).read_bytes()) for name in names}


def lean_string(value):
    if not isinstance(value, str):
        raise ValueError('expected a syntax string')
    if all((ord(c) >= 32 and ord(c) != 127) or c in '\n\r\t' for c in value):
        return json.dumps(value, ensure_ascii=False)
    return '(String.mk [' + ', '.join(f'(Char.ofNat {ord(c)})' for c in value) + '])'


def name_entry(entry):
    if set(entry) != {'name', 'identity', 'type_tag'} or not isinstance(entry['name'], str):
        raise ValueError('invalid C name-resolution entry')
    if any(type(entry[k]) is not int or entry[k] < 0 for k in ('identity', 'type_tag')):
        raise ValueError('invalid binding identity or type tag')
    return ('{ name := ' + lean_string(entry['name']) +
            f", identity := {entry['identity']}, typeTag := {entry['type_tag']}" + ' }')


def name_correspondence_proof(document):
    """Group observations by environment so their generic proof is checked once."""
    observations = document.get('name_resolution')
    if observations is None:
        raise ValueError('C export lacks binding correspondence observations')
    environments = {}
    for observation in observations:
        environment = observation['environment']
        group = environments.setdefault(canonical_json(environment), (environment, {}))
        group[1][canonical_json((observation['name'], observation['selected']))] = observation
    declarations = ['\nnamespace CBindingCorrespondence\n']
    for number, (environment, rows) in enumerate(environments.values()):
        entries = ', '.join(name_entry(entry) for entry in environment)
        declarations.append(f'def env{number} : List NLisp.CNameResolution.Entry := [{entries}]\n')
        declarations.append(
            f'theorem env{number}_valid (interpret : Nat → NLisp.ScopedSyntax.Ty) :\n'
            f'  NLisp.ScopedSyntax.Valid (NLisp.CNameResolution.scope interpret env{number}) := by\n'
            f'  change (true = true)\n  rfl\n')
        row_terms = ', '.join('{ name := ' + lean_string(row['name']) +
                              ', selected := ' + name_entry(row['selected']) + ' }'
                              for row in rows.values())
        declarations.append(f'def observations{number} : List NLisp.CNameResolution.Observation := [{row_terms}]\n')
        declarations.append(
            f'theorem observations{number}_checked :\n'
            f'  NLisp.CNameResolution.checkObservations env{number} observations{number} = true := by decide\n')
        declarations.append(
            f'theorem observations{number}_correspond :\n'
            f'  ∀ observation ∈ observations{number}, ∀ interpret : Nat → NLisp.ScopedSyntax.Ty,\n'
            f'    ∃ reference : NLisp.ScopedSyntax.Var\n'
            f'      (NLisp.ScopedSyntax.types (NLisp.CNameResolution.scope interpret env{number}))\n'
            f'      (interpret observation.selected.typeTag),\n'
            f'      NLisp.ScopedSyntax.bindingId (NLisp.CNameResolution.scope interpret env{number}) reference = observation.selected.identity :=\n'
            f'  NLisp.CNameResolution.observations_correspond env{number} observations{number} observations{number}_checked\n')
    declarations.append('end CBindingCorrespondence\n')
    return ''.join(declarations)


def natural(value, description):
    if type(value) is not int or value < 0:
        raise ValueError('invalid natural number: ' + description)
    return value


def lean_atom(node):
    if node['origin'] is not None:
        natural(node['origin'], 'definition origin')
    natural(node['token_identity'], 'token identity')
    if node.get('resolved_identity') is not None:
        natural(node['resolved_identity'], 'resolved binding identity')
    origin = 'none' if node['origin'] is None else f"(some {node['origin']})"
    return f"⟨{lean_string(node['atom'])}, {origin}, {node['token_identity']}⟩"


def copy_tree(node):
    if isinstance(node, list):
        return '(.list [' + ', '.join(copy_tree(child) for child in node) + '])'
    return f'(.atom {lean_atom(node)})'


def source_correspondence_proof(document):
    source = ', '.join(copy_tree(form) for form in document['source_ast'])
    normalized = ', '.join(copy_tree(form) for form in document['normalized_ast'])
    raw = document['source_text'].encode('utf-8')
    chunks = ['[' + ', '.join(map(str, raw[i:i + 64])) + ']' for i in range(0, len(raw), 64)]
    raw_bytes = '([' + ', '.join(chunks) + '] : List (List UInt8)).join'
    lex_fuel = len(document['source_text']) + 1
    def tokens(tree):
        return 2 + sum(map(tokens, tree)) if isinstance(tree, list) else 1
    parse_fuel = 4 * sum(map(tokens, document['source_ast'])) + 4
    return ('\nnamespace CSourceCorrespondence\n'
            f'def sourceText : String := {lean_string(document["source_text"])}\n'
            f'def sourceBytes : List UInt8 := {raw_bytes}\n'
            'theorem source_bytes_match : sourceText.toUTF8.data.data = sourceBytes := by rfl\n'
            f'def source : List NLisp.CMacroCopy.Tree := [{source}]\n'
            f'def normalized : List NLisp.CMacroCopy.Tree := [{normalized}]\n'
            f'def lexFuel : Nat := {lex_fuel}\n'
            f'def parseFuel : Nat := {parse_fuel}\n'
            'theorem source_parses : NLisp.SourceReader.readWithFuel lexFuel parseFuel sourceText = some source := by decide\n'
            'theorem source_normalizes : NLisp.SourceReader.normalize source = some normalized := by decide\n'
            'def checked : NLisp.ProcessCertificate.CheckedSource := {\n'
            '  bytes := sourceBytes, text := sourceText, lexFuel := lexFuel, parseFuel := parseFuel,\n'
            '  parsed := source, normalized := normalized,\n'
            '  bytes_match := source_bytes_match, parses := source_parses, normalizes := source_normalizes }\n'
            'end CSourceCorrespondence\n')


def copy_correspondence_proof(document):
    declarations = ['\nnamespace CCopyCorrespondence\nopen NLisp.CMacroCopy\n']
    declarations.append('def lexicalSource : List Tree := CSourceCorrespondence.source\n')
    declarations.append('def namespaceMacros := macroNames (NLisp.CExpansion.sourceRules 0 CSourceCorrespondence.normalized)\n')
    declarations.append('theorem original_atoms_have_source_ids : lexicalSource.all NLisp.CExpansion.sourceAtomsValid = true := by decide\n')
    for index, step in enumerate(document['macro_trace']):
        for key in ('definition_index', 'fresh_start', 'fresh_end'):
            natural(step[key], key)
        rule, inputs = step['rule'], step['input']
        parameters = rule[0][1:]
        if len(parameters) != len(inputs) - 1:
            raise ValueError('macro trace arity mismatch')
        holes = ', '.join(f"({lean_string(p['atom'])}, {copy_tree(a)})"
                          for p, a in zip(parameters, inputs[1:]))
        declarations.extend([
            f'def template{index} : Tree := {copy_tree(rule[3])}\n',
            f'def actual{index} : Tree := {copy_tree(step["substitution"])}\n',
            f'def holes{index} : Holes := [{holes}]\n',
        ])
        # Two units per syntax level/list element, plus helpers and empty tails.
        def nodes(tree):
            return 1 + sum(map(nodes, tree)) if isinstance(tree, list) else 1
        fuel = 4 * nodes(rule[3]) + 4
        arguments = (f'{fuel} {step["definition_index"]} holes{index} '
                     f'{step["fresh_start"]} template{index} actual{index} {step["fresh_end"]}')
        declarations.append(f'theorem substitution{index} : checkCopyWithMacros namespaceMacros {arguments} = true := by decide\n')
        declarations.append(
            f'theorem substitution{index}_sound : copyWithMacros namespaceMacros {fuel} {step["definition_index"]} '
            f'holes{index} [] {step["fresh_start"]} template{index} = '
            f'some (actual{index}, {step["fresh_end"]}) := checkCopyWithMacros_sound substitution{index}\n')
    intervals = ', '.join(f'({step["fresh_start"]}, {step["fresh_end"]})'
                          for step in document['macro_trace'])
    declarations.append(f'def intervals : List (Nat × Nat) := [{intervals}]\n')
    declarations.append('theorem fresh_counters_disjoint : NLisp.CExpansion.disjointIntervals intervals = true := by decide\n')
    declarations.append('end CCopyCorrespondence\n')
    return ''.join(declarations)


def syntax_projection(node):
    """Annotations written by the type checker are not raw syntax."""
    if isinstance(node, list):
        return [syntax_projection(child) for child in node]
    return {key: node[key] for key in ('atom', 'origin', 'token_identity')}


def expansion_correspondence_proof(document):
    declarations = ['\nnamespace CExpansionCorrespondence\n'
                    'open NLisp.CMacroCopy NLisp.CExpansion NLisp.ExpansionCertificate\n']
    declarations.append('def source : List Tree := CSourceCorrespondence.normalized\n')
    declarations.append('def rules := sourceRules 0 source\n')
    known = {}
    serial = 0

    def fresh_name():
        nonlocal serial
        name = f'certificateNode{serial}'
        serial += 1
        return name

    def define_certificate(term, accepted_proof):
        name = fresh_name()
        declarations.append(f'def {name} : Certificate := {term}\n')
        declarations.append(f'theorem {name}_accepted : check rules {name} = true := {accepted_proof}\n')
        return name

    def derive(before, after):
        before, after = syntax_projection(before), syntax_projection(after)
        if before == after:
            return define_certificate(f'Certificate.refl {copy_tree(before)}', 'by rfl')
        key = (canonical_json(before), canonical_json(after))
        if key in known:
            return known[key]
        if isinstance(before, list) and isinstance(after, list) and len(before) == len(after):
            current = list(before)
            accumulator = define_certificate(
                f'Certificate.refl (.list [{", ".join(copy_tree(item) for item in current)}])', 'by rfl')
            for position, (left, right) in enumerate(zip(before, after)):
                if left == right:
                    continue
                child = derive(left, right)
                context = define_certificate(
                    f'Certificate.congList [{", ".join(copy_tree(item) for item in current[:position])}] '
                    f'[{", ".join(copy_tree(item) for item in current[position + 1:])}] {child}',
                    f'by exact check_congList {child}_accepted')
                combined = define_certificate(
                    f'Certificate.trans {accumulator} {context}',
                    f'by exact check_trans {accumulator}_accepted {context}_accepted (by rfl)')
                current[position] = right
                accumulator = combined
            return accumulator
        raise ValueError('expansion trace does not derive the exported syntax')

    for index, step in enumerate(document['macro_trace']):
        for field in ('rule', 'input', 'result'):
            declarations.append(f'def {field}{index} : Tree := {copy_tree(step[field])}\n')
        def nodes(tree):
            return 1 + sum(map(nodes, tree)) if isinstance(tree, list) else 1
        fuel = 4 * nodes(step['rule'][3]) + 4
        macro_cert = f'macroCert{index}'
        declarations.append(f'def {macro_cert} : Certificate := Certificate.macroStep '
                            f'{step["definition_index"]} {fuel} {step["fresh_start"]} {step["fresh_end"]} '
                            f'rule{index} input{index} CCopyCorrespondence.actual{index}\n')
        declarations.append(f'theorem {macro_cert}_accepted : check rules {macro_cert} = true := by\n'
                            f'  simpa [{macro_cert}, check] using\n'
                            f'    checkStep_intro (rules := rules) (by decide) (by decide) '
                            f'CCopyCorrespondence.substitution{index}_sound\n')
        inner = derive(step['substitution'], step['result'])
        expanded_cert = f'expandedCert{index}'
        declarations.append(f'def {expanded_cert} : Certificate := Certificate.trans {macro_cert} {inner}\n')
        declarations.append(f'theorem {expanded_cert}_accepted : check rules {expanded_cert} = true := by\n'
                            f'  exact check_trans {macro_cert}_accepted {inner}_accepted (by rfl)\n')
        known[(canonical_json(syntax_projection(step['input'])),
               canonical_json(syntax_projection(step['result'])))] = expanded_cert
    raw = [form for form in document['normalized_ast'] if atom(form[0]) != 'define-macro']
    result = document['declarations']
    derivation = derive(raw, result)
    declarations.append('def expanded : List Tree := [' + ', '.join(copy_tree(form) for form in result) + ']\n')
    declarations.append(f'def programCertificate : Certificate := {derivation}\n')
    declarations.append('theorem program_certificate_accepted : check rules programCertificate = true :=\n'
                        f'  {derivation}_accepted\n')
    declarations.append('theorem program_certificate_fresh :\n'
                        '  disjointIntervals (freshIntervals programCertificate) = true := by decide\n')
    declarations.append('theorem program_certificate_fresh_accepted :\n'
                        '  checkFresh rules programCertificate = true :=\n'
                        '  checkFresh_intro program_certificate_fresh program_certificate_accepted\n')
    declarations.append('theorem program_expands :\n'
                        '  Expands rules (.list (programForms source)) (.list expanded) := by\n'
                        '  exact checkFresh_sound programCertificate program_certificate_fresh_accepted\n')
    declarations.append('end CExpansionCorrespondence\n')
    return ''.join(declarations)


def binding_tree(node):
    if isinstance(node, list):
        return '(.list [' + ', '.join(binding_tree(child) for child in node) + '])'
    return f'(.atom {lean_atom(node)} {node["resolved_identity"] or 0})'


def binding_walk_proof(document):
    forms = document['declarations']
    def nodes(tree):
        return 1 + sum(map(nodes, tree)) if isinstance(tree, list) else 1
    fuel = 4 * nodes(forms) + 4
    syntax = ', '.join(binding_tree(form) for form in forms)
    return (f'\nnamespace CProgramScope\nopen NLisp.CBindingWalk\n'
            f'def forms : List Node := [{syntax}]\n'
            'theorem scope_syntax_is_expansion : forms.map Node.erase = CExpansionCorrespondence.expanded := by decide\n'
            f'theorem checked : check {fuel} forms builtinEnvironment = true := by decide\n'
            f'theorem all_references_correspond :\n'
            f'  ∃ sites, references {fuel} forms builtinEnvironment = some sites ∧\n'
            f'    ∀ site ∈ sites, Corresponds site :=\n'
            f'  check_sound {fuel} forms builtinEnvironment checked\n'
            f'end CProgramScope\n')


def syntax_nodes(tree):
    return 1 + sum(map(syntax_nodes, tree)) if isinstance(tree, list) else 1


def termination_plan(document, max_steps=100000):
    """Untrusted rank synthesis; Lean re-extracts every edge and checks decreases."""
    work = 0

    def spend(count=1):
        nonlocal work
        if count < 0 or count > max_steps - work:
            attempted = work + count
            raise UnknownResult(
                'termination analysis conversion step limit exceeded '
                f'(attempted {attempted}, limit {max_steps})')
        work += count

    rules, declaration_index = [], 0
    for form in document['normalized_ast']:
        spend()
        if atom(form[0]) == 'define-macro':
            for rule in form[2][1:]:
                spend()
                rules.append((declaration_index, rule))
        else:
            declaration_index += 1
    signatures = []
    for _, rule in rules:
        spend()
        signatures.append((atom(rule[0][0]), len(rule[0]) - 1))
    edges = []
    try:
        for parent, (_, rule) in enumerate(rules):
            spend()
            spend(len(rule[0]))
            holes = {atom(parameter) for parameter in rule[0][1:]}

            def candidates(predicate):
                matches = []
                for target, signature in enumerate(signatures):
                    spend()
                    if predicate(signature):
                        matches.append(target)
                return matches

            def calls(tree):
                spend()
                if not isinstance(tree, list):
                    return []
                nested = [target for child in tree for target in calls(child)]
                if tree and atom(tree[0]) is not None:
                    name = atom(tree[0])
                    if name in holes:
                        arity = len(tree) - 1
                        return candidates(lambda signature: signature[1] == arity) + nested
                    arity = len(tree) - 1
                    return candidates(lambda signature: signature == (name, arity)) + nested
                return nested
            for child in calls(rule[3]):
                spend()
                edges.append((child, parent))
    except ValueError as error:
        return dict(status='unknown', reason=str(error), rules=signatures)
    spend(5 * len(rules))
    dependencies = [set() for _ in rules]
    parents = [set() for _ in rules]
    for child, parent in edges:
        spend()
        dependencies[parent].add(child)
        parents[child].add(parent)
    remaining = [len(children) for children in dependencies]
    queue = [index for index, count in enumerate(remaining) if count == 0]
    ranks = [0] * len(rules)
    for child in queue:
        spend()
        for parent in parents[child]:
            spend()
            ranks[parent] = max(ranks[parent], ranks[child] + 1)
            remaining[parent] -= 1
            if remaining[parent] == 0:
                queue.append(parent)
    if len(queue) != len(rules):
        return dict(status='unknown', reason='no decreasing rank found for recursive rule dependencies',
                    rules=signatures, edges=edges)
    return dict(status='proved', rules=signatures, edges=edges, ranks=ranks,
                guarantee='well-founded conservative macro call candidate graph')


def termination_correspondence_proof(document, plan, standalone=False):
    declarations = ['\nnamespace CMacroTermination\nopen NLisp.MacroTermination\n']
    if standalone:
        declarations.append('def source : List NLisp.CMacroCopy.Tree := CSourceCorrespondence.normalized\n')
        declarations.append('def rules := NLisp.CExpansion.sourceRules 0 source\n')
    else:
        declarations.append('def rules := CExpansionCorrespondence.rules\n')
    declarations.append(f'def status : String := {lean_string(plan["status"])}\n')
    if plan['status'] == 'proved':
        edges = ', '.join(f'({child}, {parent})' for child, parent in plan['edges'])
        ranks = ', '.join(map(str, plan['ranks']))
        fuel = 4 * syntax_nodes(document['normalized_ast']) + 4
        declarations.extend([
            f'def edges : List Edge := [{edges}]\n',
            f'def ranks : List Nat := [{ranks}]\n',
            f'theorem graph_matches_source : graph {fuel} rules = some edges := by decide\n',
            'theorem rank_checked : checkRanks edges ranks = true := by decide\n',
            'theorem rule_calls_wellFounded : WellFounded (Calls edges) :=\n'
            '  ranked_graph_wellFounded rank_checked\n',
            'theorem every_call_chain_bounded (path : Path edges first last count) :\n'
            '    count + rank ranks last ≤ rank ranks first :=\n'
            '  path_length_bounded rank_checked path\n',
            f'theorem every_static_rule_call_decreases (edge : Edge)\n'
            f'    (call : GraphCall rules 0 rules edge) :\n'
            f'    rank ranks edge.1 < rank ranks edge.2 := by\n'
            f'  apply checkRanks_decreases rank_checked\n'
            f'  exact graphRows_contains_static_calls {fuel} rules 0 rules edges graph_matches_source call\n',
        ])
    else:
        declarations.append(f'def reason : String := {lean_string(plan["reason"])}\n')
    declarations.append('end CMacroTermination\n')
    return ''.join(declarations)


def process_correspondence_proof(document, mode):
    if mode == 'termination':
        fuel = 4 * syntax_nodes(document['normalized_ast']) + 4
        return ('\nnamespace VerifiedNLispSource\n'
                'def certificate : NLisp.ProcessCertificate.CheckedStaticTermination := {\n'
                '  toCheckedSource := CSourceCorrespondence.checked,\n'
                f'  graphFuel := {fuel}, edges := CMacroTermination.edges, ranks := CMacroTermination.ranks,\n'
                '  graph_matches := CMacroTermination.graph_matches_source,\n'
                '  decreases := CMacroTermination.rank_checked }\n'
                'theorem source_rules_wellFounded :\n'
                '  NLisp.MacroTermination.graph certificate.graphFuel\n'
                '    (NLisp.CExpansion.sourceRules 0 certificate.normalized) = some certificate.edges ∧\n'
                '  WellFounded (NLisp.MacroTermination.Calls certificate.edges) :=\n'
                '  NLisp.ProcessCertificate.source_rules_wellFounded certificate\n'
                'end VerifiedNLispSource\n')
    fuel = 4 * syntax_nodes(document['declarations']) + 4
    return ('\nnamespace VerifiedNLispSource\n'
            'def certificate : NLisp.ProcessCertificate.CheckedExpansion := {\n'
            '  toCheckedSource := CSourceCorrespondence.checked,\n'
            '  expanded := CExpansionCorrespondence.expanded, annotated := CProgramScope.forms,\n'
            f'  scopeFuel := {fuel}, expands := CExpansionCorrespondence.program_expands,\n'
            '  same_syntax := CProgramScope.scope_syntax_is_expansion,\n'
            '  scope_checks := CProgramScope.all_references_correspond }\n'
            'theorem source_expands_with_scopes :\n'
            '  certificate.text.toUTF8.data.data = certificate.bytes ∧\n'
            '  NLisp.SourceReader.readWithFuel certificate.lexFuel certificate.parseFuel certificate.text = some certificate.parsed ∧\n'
            '  NLisp.SourceReader.normalize certificate.parsed = some certificate.normalized ∧\n'
            '  NLisp.CExpansion.Expands (NLisp.CExpansion.sourceRules 0 certificate.normalized)\n'
            '    (.list (NLisp.CExpansion.programForms certificate.normalized)) (.list certificate.expanded) ∧\n'
            '  certificate.annotated.map NLisp.CBindingWalk.Node.erase = certificate.expanded ∧\n'
            '  ∃ sites, NLisp.CBindingWalk.references certificate.scopeFuel certificate.annotated\n'
            '      NLisp.CBindingWalk.builtinEnvironment = some sites ∧\n'
            '    ∀ site ∈ sites, NLisp.CBindingWalk.Corresponds site :=\n'
            '  NLisp.ProcessCertificate.source_expands_with_scopes certificate\n'
            'end VerifiedNLispSource\n')


def render_proof(document, mode, budget):
    if mode == 'termination':
        source_nodes = syntax_nodes(document['normalized_ast'])
        if source_nodes > budget['max_conversion_steps']:
            raise UnknownResult(
                'termination analysis source node limit exceeded '
                f'({source_nodes} nodes, limit {budget["max_conversion_steps"]})')
        plan = termination_plan(document, budget['max_conversion_steps'])
        if plan['status'] != 'proved':
            raise UnknownResult('conservative macro call candidate graph: ' + plan['reason'])
        proof = ('import NLisp\nset_option maxRecDepth 4096\nset_option maxHeartbeats 2000000\n' +
                 source_correspondence_proof(document) +
                 termination_correspondence_proof(document, plan, standalone=True) +
                 process_correspondence_proof(document, 'termination'))
        if len(proof.encode('utf-8')) > budget['max_certificate_bytes']:
            raise UnknownResult('termination proof size limit exceeded')
        return proof, [{'stage': 'macro_termination', **plan}]
    cls = {'types': TypeExporter, 'poly': PolyExporter}.get(mode, Exporter)
    exporter = cls(document, record_process=True, **budget)
    try:
        plan = termination_plan(document, budget['max_conversion_steps'])
    except UnknownResult as error:
        plan = dict(status='unknown', reason=str(error), rules=[])
    proof = (exporter.export().replace('import NLisp\n',
             'import NLisp\nset_option maxRecDepth 4096\nset_option maxHeartbeats 2000000\n', 1) +
             source_correspondence_proof(document) + name_correspondence_proof(document) +
             copy_correspondence_proof(document) + expansion_correspondence_proof(document) +
             binding_walk_proof(document) + termination_correspondence_proof(document, plan) +
             process_correspondence_proof(document, mode))
    if mode == 'poly':
        proof += ('\nnamespace VerifiedPolyProgram\n'
                  'theorem source_lowering_checked :\n'
                  '    NLisp.ExpansionLowering.checkProgram 512 CProgramScope.forms signatures bodies = true := by decide\n'
                  'theorem main_is_entry : NLisp.ExpansionLowering.checkMain 512 CProgramScope.forms ' + str(exporter.indices['main']) + ' = true := by decide\n'
                  'theorem program_typed : NLisp.PolyIR.ProgramTyped signatures source :=\n'
                  '  NLisp.Surface.elaborateProgram_programTyped all_bodies_check\n'
                  'theorem entry_has_no_type_error (fuel : Nat) (fault : NLisp.PolyIR.Fault)\n'
                  '    (h : NLisp.PolyIR.evaluate program.erase fuel [] (NLisp.PolyIR.erase entry) = .error fault) :\n'
                  '    fault = .outOfFuel := by\n'
                  '  rw [program_erasure] at h\n'
                  '  exact NLisp.PolyIR.evaluation_no_type_error program_typed\n'
                  '    (NLisp.Surface.elaborate_typed entry_checks)\n'
                  '    (assignment := fun _ => Ty.unit) (by simpa only [NLisp.Surface.interpretTypes] using NLisp.PolyIR.ValuesTyped.nil) h\n'
                  'def decoded := NLisp.Named.decodeProgram 512 CProgramScope.forms\n'
                  'theorem source_decodes : decoded.isSome = true := by decide\n'
                  'def namedSource : NLisp.Named.Definitions := decoded.get source_decodes\n'
                  'theorem lowered_source_matches : NLisp.Named.lowerDefinitions namedSource = program.erase := by rfl\n'
                  'def namedEntry : NLisp.Named.Expr := .app (.global ' + str(exporter.indices['main']) + ') []\n'
                  'theorem source_evaluation_preserved {value : NLisp.Named.Value}\n'
                  '    (h : NLisp.Named.Evaluates namedSource [] namedEntry value) :\n'
                  '    NLisp.PolyIR.Evaluates program.erase [] (NLisp.PolyIR.erase entry) (NLisp.Named.lowerValue value) := by\n'
                  '  have preserved := NLisp.Named.evaluation_preserved h\n'
                  '  simpa [lowered_source_matches, namedEntry, entry, NLisp.Named.lowerEnv,\n'
                  '    NLisp.Named.lower, NLisp.Named.identities] using preserved\n'
                  'end VerifiedPolyProgram\n')
    exporter.check_term(proof)
    exporter.record_event({'stage': 'macro_termination', **plan})
    return proof, exporter.process


def pack_bundle(source, document, process, proof, mode, budget):
    expected_format = 'nlisp-syntax-v1' if mode == 'termination' else 'nlisp-scoped-expansion-v2'
    if document.get('format') != expected_format:
        raise ValueError('unexpected process evidence format')
    manifest = {
        'format': 'nlisp-process-certificate-v1',
        'source': {'encoding': 'base64', 'bytes': base64.b64encode(source).decode('ascii'),
                   'sha256': digest(source)},
        'expansion': {'document': document,
                      'sha256': digest(canonical_json(document).encode('utf-8'))},
        'conversion': {'mode': mode, 'events': process, 'limits': budget},
        'lean': {'body_sha256': digest(proof.encode('utf-8'))},
        'environment': environment_hashes(), 'assurance': assurance_for(mode),
    }
    payload = canonical_json(manifest).encode('utf-8')
    encoded = base64.b64encode(payload).decode('ascii')
    lines = ''.join('-- ' + encoded[i:i + 100] + '\n' for i in range(0, len(encoded), 100))
    return (BUNDLE_HEADER + BUNDLE_HASH + digest(payload) + '\n' +
            BUNDLE_BEGIN + lines + BUNDLE_END + proof)


def reject_duplicate_keys(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise ValueError('duplicate certificate field: ' + name)
        result[name] = value
    return result


def unpack_bundle(text):
    lines = text.splitlines(keepends=True)
    if len(lines) < 5 or lines[0] != BUNDLE_HEADER or lines[2] != BUNDLE_BEGIN:
        raise ValueError('not an NLisp process certificate')
    if not re.fullmatch(re.escape(BUNDLE_HASH) + r'[0-9a-f]{64}\n', lines[1]):
        raise ValueError('invalid payload digest')
    end = lines.index(BUNDLE_END, 3)
    parts = []
    for line in lines[3:end]:
        if not line.startswith('-- ') or not line.endswith('\n'):
            raise ValueError('invalid certificate payload line')
        parts.append(line[3:-1])
    payload = base64.b64decode(''.join(parts), validate=True)
    if digest(payload) != lines[1][len(BUNDLE_HASH):].strip():
        raise ValueError('certificate payload digest mismatch')
    manifest = json.loads(payload, object_pairs_hook=reject_duplicate_keys)
    proof = ''.join(lines[end + 1:])
    if set(manifest) != {'format', 'source', 'expansion', 'conversion', 'lean', 'environment', 'assurance'}:
        raise ValueError('invalid certificate manifest fields')
    mode = manifest['conversion']['mode']
    if mode not in ('core', 'types', 'poly', 'termination'):
        raise ValueError('invalid proof mode')
    if manifest['format'] != 'nlisp-process-certificate-v1' or manifest['assurance'] != assurance_for(mode):
        raise ValueError('unsupported certificate format or assurance claim')
    if digest(proof.encode('utf-8')) != manifest['lean']['body_sha256']:
        raise ValueError('Lean body digest mismatch')
    return manifest, proof


def replay_bundle(path, args):
    text = read_bounded_file(path, args.max_certificate_bytes).decode('utf-8')
    manifest, proof = unpack_bundle(text)
    if manifest['environment'] != environment_hashes():
        raise ValueError('Lean specification or toolchain files differ from certificate environment')
    if manifest['source']['encoding'] != 'base64':
        raise ValueError('unsupported source encoding')
    source = base64.b64decode(manifest['source']['bytes'], validate=True)
    if digest(source) != manifest['source']['sha256']:
        raise ValueError('embedded source digest mismatch')
    document = manifest['expansion']['document']
    if document.get('source_text', '').encode('utf-8') != source:
        raise ValueError('embedded source bytes differ from the proof document source')
    mode = manifest['conversion']['mode']
    expected_format = 'nlisp-syntax-v1' if mode == 'termination' else 'nlisp-scoped-expansion-v2'
    if document.get('format') != expected_format:
        raise ValueError('unexpected process evidence format')
    if digest(canonical_json(document).encode('utf-8')) != manifest['expansion']['sha256']:
        raise ValueError('expanded process digest mismatch')
    limits = document['limits']
    if set(limits) != set(C_LIMITS):
        raise ValueError('invalid expansion limits')
    for name, default in C_LIMITS.items():
        value = limits[name]
        policy = getattr(args, name)
        policy = default if policy is None else policy
        if type(value) is not int or value < 0:
            raise ValueError('invalid expansion budget')
        if value > policy:
            raise UnknownResult(f'certificate requires {name}={value}, policy limit is {policy}')
    budget = manifest['conversion']['limits']
    if set(budget) != {'max_certificate_bytes', 'max_conversion_steps'}:
        raise ValueError('invalid conversion limits')
    for name, value in budget.items():
        if type(value) is not int or value < 0:
            raise ValueError('invalid conversion budget')
        if value > getattr(args, name):
            raise UnknownResult('certificate conversion budget exceeds verifier policy: ' + name)
    mode = manifest['conversion']['mode']
    if mode not in ('core', 'types', 'poly', 'termination'):
        raise ValueError('invalid proof mode')
    if getattr(args, 'independent', False):
        # No C executable, macro expander, or source evaluator is invoked.
        # The recorded local rule applications generate proof obligations;
        # SourceReader, CExpansion and CBindingWalk independently check them.
        replayed = document
    else:
        with tempfile.TemporaryDirectory(prefix='nlisp-replay-') as directory:
            input_path = pathlib.Path(directory) / 'source.nlisp'
            input_path.write_bytes(source)
            command = [args.nlisp, 'export-syntax' if mode == 'termination' else 'export-core', str(input_path)]
            for name, value in limits.items():
                command.extend(['--' + name.replace('_', '-'), str(value)])
            result = run_export(command, args.max_certificate_bytes)
            if result.returncode == 7:
                raise UnknownResult(result.stderr.strip())
            result.check_returncode()
            replayed = json.loads(result.stdout)
        if canonical_json(replayed) != canonical_json(document):
            raise ValueError('source parsing, normalization, or macro expansion trace does not replay')
    expected, process = render_proof(replayed, mode, budget)
    if expected != proof or canonical_json(process) != canonical_json(manifest['conversion']['events']):
        raise ValueError('conversion trace or Lean body does not match the expanded program')
    verify_certificate(text, path, args.lake, publish=False)
    return mode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=pathlib.Path, nargs='?')
    parser.add_argument('--nlisp', default='build/nlisp')
    parser.add_argument('--output', type=pathlib.Path)
    parser.add_argument('--verify-certificate', type=pathlib.Path)
    parser.add_argument('--independent', action='store_true',
                        help='verify a certificate using recorded local derivations and Lean, without running the C expander')
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--mode', choices=('auto', 'core', 'types', 'poly', 'termination'), default='auto',
                        help='auto/core/types use legacy cores; poly checks shared generic bodies; termination proves a conservative macro call candidate graph without expanding')
    for option in ('max-expansions', 'max-generated-nodes', 'max-expansion-depth', 'max-check-steps'):
        parser.add_argument('--' + option, type=int)
    parser.add_argument('--max-certificate-bytes', type=int, default=4194304)
    parser.add_argument('--max-conversion-steps', type=int, default=100000)
    args = parser.parse_args()
    if args.independent and args.verify_certificate is None:
        parser.error('--independent requires --verify-certificate')
    if args.verify_certificate is not None:
        if args.source is not None or args.output is not None:
            parser.error('--verify-certificate takes no source or output path')
    elif args.source is None or args.output is None:
        parser.error('generation requires a source and --output')
    try:
        for name in ('max_certificate_bytes', 'max_conversion_steps', *C_LIMITS):
            value = getattr(args, name)
            if value is not None and value < 0:
                raise ValueError('resource limits must be nonnegative')
        if args.verify_certificate is not None:
            mode = replay_bundle(args.verify_certificate, args)
            method = 'Independent certificate' if args.independent else 'Process replay'
            print(f'{method} and Lean {mode} check passed: {args.verify_certificate}')
            return 0
        source_bytes = read_bounded_file(args.source, args.max_certificate_bytes)
        command = [args.nlisp, 'export-syntax' if args.mode == 'termination' else 'export-core', str(args.source)]
        for option in ('max_expansions', 'max_generated_nodes', 'max_expansion_depth', 'max_check_steps'):
            value = getattr(args, option)
            if value is not None:
                if value < 0:
                    raise ValueError('limits must be nonnegative')
                command.extend(['--' + option.replace('_', '-'), str(value)])
        result = run_export(command, args.max_certificate_bytes)
        if result.returncode == 7:
            raise UnknownResult(result.stderr.strip())
        result.check_returncode()
        if read_bounded_file(args.source, args.max_certificate_bytes) != source_bytes:
            raise ValueError('source changed during scoped expansion')
        document = json.loads(result.stdout)
        if document['source_text'].encode('utf-8') != source_bytes:
            raise ValueError('source text in C export differs from the embedded source bytes')
        if args.max_certificate_bytes < 0 or args.max_conversion_steps < 0:
            raise ValueError('certificate limits must be nonnegative')
        budget = dict(max_certificate_bytes=args.max_certificate_bytes,
                      max_conversion_steps=args.max_conversion_steps)
        mode = args.mode
        if mode in ('types', 'poly', 'termination'):
            certificate, process = render_proof(document, mode, budget)
        else:
            try:
                certificate, process = render_proof(document, 'core', budget)
                mode = 'core'
            except ValueError:
                if mode == 'core':
                    raise
                certificate, process = render_proof(document, 'types', budget)
                mode = 'types'
        certificate = pack_bundle(source_bytes, document, process, certificate, mode, budget)
        if len(certificate.encode('utf-8')) > args.max_certificate_bytes:
            raise UnknownResult(f'certificate size limit ({args.max_certificate_bytes} bytes) exceeded')
        verify_certificate(certificate, args.output, args.lake)
    except (UnknownResult, RecursionError) as error:
        print(f'Unknown: no certificate issued: {error}', file=sys.stderr)
        return 7
    except (ValueError, TypeError, AttributeError, KeyError, IndexError, OSError, subprocess.CalledProcessError) as error:
        print(f'Lean verification failed: {error}', file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError) and error.stderr:
            print(error.stderr, file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError) and error.stdout:
            print(error.stdout, file=sys.stderr)
        return 1
    kind = 'conservative macro call candidate graph' if mode == 'termination' else 'expanded ' + mode
    print(f'Lean checked {kind} certificate: {args.output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
