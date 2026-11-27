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


def run_lean_command(command, env=None):
    root = pathlib.Path(__file__).resolve().parents[1]
    result = subprocess.run(command, cwd=root, env=env, capture_output=True, encoding='utf-8')
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


def split_lean_namespaces(source):
    """Keep each generated top-level namespace in a separate Lean module.

    Certificate proofs often contain large executable checks. Isolating each
    namespace lets Lean release elaboration memory between those checks while
    preserving every declaration and its kernel-checked proof.
    """
    lines = source.splitlines(keepends=True)
    preamble, blocks, current = [], [], []
    depth = 0
    for line in lines:
        stripped = line.strip()
        if depth == 0 and re.fullmatch(r'namespace [A-Za-z_][A-Za-z0-9_.]*', stripped):
            if current:
                blocks.append(''.join(current))
                current = []
            current.append(line)
            depth = 1
            continue
        if depth == 0:
            preamble.append(line)
            continue
        current.append(line)
        if re.fullmatch(r'namespace [A-Za-z_][A-Za-z0-9_.]*', stripped):
            depth += 1
        elif re.fullmatch(r'end(?: [A-Za-z_][A-Za-z0-9_.]*)?', stripped):
            depth -= 1
            if depth == 0:
                blocks.append(''.join(current))
                current = []
    if current:
        raise ValueError('generated Lean certificate has an unclosed namespace')
    preamble_text = ''.join(preamble)
    if not blocks:
        return preamble_text, []
    if not preamble_text.strip().startswith('import NLisp'):
        raise ValueError('unexpected top-level content in generated Lean certificate')
    return preamble_text, blocks


def check_lean_modular(proof, names, lake, directory):
    """Compile generated namespace blocks separately, then audit all theorem axioms."""
    root = pathlib.Path(directory)
    module_dir = root / 'NlispCertificate'
    module_dir.mkdir(parents=True, exist_ok=True)
    inherited_path = os.environ.get('LEAN_PATH', '')
    env = os.environ.copy()
    env['LEAN_PATH'] = str(root) + (os.pathsep + inherited_path if inherited_path else '')
    preamble, blocks = split_lean_namespaces(proof)
    # Top-level declarations belong only to the first module. Repeating the
    # whole preamble after importing the previous chunk redeclares names such
    # as `expandedProgram`; only namespace-independent commands need to be
    # carried forward.
    shared_commands = ''.join(
        line for line in preamble.splitlines(keepends=True)
        if re.match(r'^(?:open\b|set_option\b)', line))
    expanded_blocks = []
    for block in blocks:
        namespace_match = re.match(r'namespace ([A-Za-z_][A-Za-z0-9_.]*)\n', block)
        if namespace_match is None:
            expanded_blocks.append(block)
            continue
        namespace = namespace_match[1]
        body = block[namespace_match.end():]
        body = re.sub(r'end ' + re.escape(namespace) + r'\s*$', '', body)
        starts = [match.start() for match in re.finditer(
            r'^(?:open|(?:noncomputable )?def|theorem|abbrev|structure|inductive)\b',
            body, re.MULTILINE)]
        if not starts:
            expanded_blocks.append(block)
            continue
        commands = []
        for position, start in enumerate(starts):
            finish = starts[position + 1] if position + 1 < len(starts) else len(body)
            command = body[start:finish].strip()
            if command:
                commands.append(command)
        namespace_opens = [command for command in commands if command.startswith('open ')]
        declarations = [command for command in commands if not command.startswith('open ')]
        for offset in range(0, len(declarations), 4):
            chunk = declarations[offset:offset + 4]
            expanded_blocks.append(
                f'namespace {namespace}\n' + '\n'.join(namespace_opens) +
                '\n' + '\n'.join(chunk) + f'\nend {namespace}\n')
    blocks = expanded_blocks
    previous = None
    for index, block in enumerate(blocks):
        module = f'NlispCertificate.Part{index}'
        source_path = module_dir / f'Part{index}.lean'
        object_path = module_dir / f'Part{index}.olean'
        imports = preamble if previous is None else f'import {previous}\n{shared_commands}'
        module_source = imports + block
        if not (object_path.exists() and source_path.exists() and
                source_path.read_text(encoding='utf-8') == module_source):
            source_path.write_text(module_source, encoding='utf-8')
            try:
                run_lean_command([lake, 'env', 'lean', '-o', str(object_path), str(source_path)], env=env)
            except subprocess.CalledProcessError as error:
                lines = module_source.splitlines()
                excerpt = '\n'.join(f'{line_no + 1}: {lines[line_no]}'
                                    for line_no in range(max(0, 27), min(len(lines), 42)))
                diagnostics = (error.stdout or '') + (error.stderr or '')
                raise ValueError(f'{diagnostics}\nGenerated module {module}:\n{excerpt}') from error
        previous = module
    audit_path = root / 'Audit.lean'
    audit_path.write_text(
        f'import {previous}\n' + ''.join('#print axioms ' + name + '\n' for name in names),
        encoding='utf-8')
    result = run_lean_command([lake, 'env', 'lean', str(audit_path)], env=env)
    check_generated_axioms(result.stdout, names)


STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound', 'Lean.ofReduceBool'}


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
    audit = re.compile(
        r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
        re.DOTALL)
    for match in audit.finditer(output):
        dependencies = {name.strip() for name in match[3].split(',') if name.strip()} if match[3] else set()
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
        manifest, proof = unpack_bundle(certificate)
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
        if not certificate.startswith(BUNDLE_HEADER):
            proof = certificate
        with tempfile.TemporaryDirectory(prefix='NlispCertificateModules_',
                                         dir=root / '.lake' / 'build') as directory:
            check_lean_modular(proof, names, lake, directory)
        if snapshot != environment_hashes():
            raise ValueError('Lean model files changed during certificate verification')
        if publish:
            with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', newline='', suffix='.lean',
                                             prefix='NlispCertificate_', dir=output.parent,
                                             delete=False) as stream:
                staged = pathlib.Path(stream.name).resolve()
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


def verify_builtin_table():
    """Check C's executable builtin signatures against the Lean exporter table.

    `TypeExporter` turns each entry in PRIMITIVES into a typed Lean builtin
    expression. This check pins those names, operations, homogeneous argument
    types, result types, optional-result flags, and arities to the C runtime
    registration table before any certificate is accepted or generated.
    """
    root = pathlib.Path(__file__).resolve().parents[1]
    source = (root / 'src/nlisp.c').read_text(encoding='utf-8')
    binding_walk = (root / 'NLisp/CBindingWalk.lean').read_text(encoding='utf-8')
    apply_start = source.find('static Value *apply(Runtime *r, Value *f, Value **args, size_t n, Span span) {')
    eval_start = source.find('static Value *eval(Runtime *r, const SExpr *x, RBind *env) {', apply_start)
    if apply_start < 0 or eval_start < 0:
        raise ValueError('C builtin apply implementation was not found')
    builtin_apply = source[apply_start:eval_start]
    # Text is length-bearing: equality must compare both lengths and exactly
    # that many bytes, while append must copy each full payload including NUL.
    string_equal_contract = re.compile(
        r'args\[0\]->as\.text\.length\s*==\s*args\[1\]->as\.text\.length\s*&&\s*'
        r'memcmp\(args\[0\]->as\.text\.data,\s*args\[1\]->as\.text\.data,\s*'
        r'args\[0\]->as\.text\.length\)\s*==\s*0', re.S)
    string_append_contract = re.compile(
        r'v->as\.text\.length\s*=\s*left\.length\s*\+\s*right\.length\s*;'
        r'.*?memcpy\(v->as\.text\.data,\s*left\.data,\s*left\.length\)\s*;'
        r'.*?memcpy\(v->as\.text\.data\s*\+\s*left\.length,\s*right\.data,\s*right\.length\)', re.S)
    if string_equal_contract.search(builtin_apply) is None:
        raise ValueError('C string= no longer compares length-bearing Text bytes')
    if string_append_contract.search(builtin_apply) is None:
        raise ValueError('C string-append no longer copies both full length-bearing Text payloads')
    marker = 'static const BuiltinSpec builtin_specs[] = {'
    if marker not in source:
        raise ValueError('C builtin_specs table was not found')
    table = source.split(marker, 1)[1].split('};', 1)[0]
    row_pattern = re.compile(
        r'\{\s*"([^"]+)"\s*,\s*(BI_[A-Z_]+)\s*,\s*'
        r'(TY_[A-Z_]+)\s*,\s*(TY_[A-Z_]+)\s*,\s*(\d+)U\s*,\s*'
        r'(true|false)\s*\}'
    )
    # Parse every initializer as a complete row. `findall` alone would accept
    # a partial table if a changed or malformed C row stopped matching.
    initializers = re.findall(r'\{[^{}]*\}', table)
    rows = []
    for initializer in initializers:
        match = row_pattern.fullmatch(initializer.strip())
        if match is None:
            raise ValueError(f'unrecognized C builtin_specs row: {initializer!r}')
        rows.append(match.groups())
    if not rows:
        raise ValueError('C builtin_specs table contains no recognizable rows')

    # Builtin identities are the enum ordinals, and the Lean name table is
    # ordered by these same ordinals. Pin the enum itself to the complete
    # registration order so an unregistered enum member or an enum/table
    # reorder cannot silently preserve a misleading dispatcher-reference set.
    enum_start = source.find('typedef enum {\n    BI_ADD')
    enum_end = source.find('} Builtin;', enum_start)
    if enum_start < 0 or enum_end < 0:
        raise ValueError('C Builtin enum was not found')
    enum_block = source[enum_start:enum_end]
    enum_operations = re.findall(r'\bBI_[A-Z_]+\b', enum_block)
    registered_operations_in_order = [operation for _name, operation, *_rest in rows]
    if enum_operations != registered_operations_in_order:
        raise ValueError('C Builtin enum order/set differs from builtin_specs registration order: '
                         f'enum={enum_operations!r}, table={registered_operations_in_order!r}')

    primitive_by_name = {name: (primitive, input_type, output_type, arity)
                         for name, primitive, input_type, output_type, arity in PRIMITIVES}

    # Check the actual independent Lean type function as well as the exporter
    # metadata above. Parse its small closed type language and compare every
    # primitive's curried type to the C registration signature.
    typed_expansion = (root / 'NLisp/TypedExpansion.lean').read_text(encoding='utf-8')
    type_start = typed_expansion.find('def Primitive.type : Primitive → Ty')
    type_end = typed_expansion.find('/-- Signed integer division', type_start)
    if type_start < 0 or type_end < 0:
        raise ValueError('Lean Primitive.type definition was not found')
    type_block = typed_expansion[type_start:type_end]
    lean_primitive_types = {}

    def parse_type_expression(expression):
        tokens = re.findall(
            r'\.|\b(?:binary|fn|option|boolean|integer|unit|floating|string|character)\b|[()]',
            expression)
        tokens = [token for token in tokens if token != '.']
        position = 0

        def parse_one():
            nonlocal position
            if position >= len(tokens):
                raise ValueError(f'incomplete Lean primitive type expression: {expression!r}')
            token = tokens[position]
            position += 1
            if token == '(':
                result = parse_one()
                if position >= len(tokens) or tokens[position] != ')':
                    raise ValueError(f'unclosed Lean primitive type expression: {expression!r}')
                position += 1
                return result
            atoms = {'boolean': 'Boolean', 'integer': 'Integer', 'unit': 'Unit',
                     'floating': 'Float', 'string': 'String', 'character': 'Character'}
            if token in atoms:
                return atoms[token]
            if token == 'option':
                return ('Option', parse_one())
            if token == 'fn':
                return ('Function', parse_one(), parse_one())
            if token == 'binary':
                argument = parse_one()
                result = parse_one()
                return ('Function', argument, ('Function', argument, result))
            raise ValueError(f'unknown Lean primitive type token {token!r}')

        result = parse_one()
        if position != len(tokens):
            raise ValueError(f'extra Lean primitive type tokens in {expression!r}')
        return result

    branch_pattern = re.compile(r'^\s*\|\s*([^=]+?)\s*=>\s*(.+?)\s*$', re.MULTILINE)
    for lhs, rhs in branch_pattern.findall(type_block):
        operations = re.findall(r'\.([A-Za-z][A-Za-z0-9]*)', lhs)
        parsed_type = parse_type_expression(rhs)
        for operation in operations:
            if operation in lean_primitive_types:
                raise ValueError(f'duplicate Lean primitive type case: {operation}')
            lean_primitive_types[operation] = parsed_type

    def curried_type(input_type, output_type, arity):
        result = output_type
        for _ in range(arity):
            result = ('Function', input_type, result)
        return result

    expected_primitive_types = {
        primitive: curried_type(input_type, output_type, arity)
        for primitive, input_type, output_type, arity in primitive_by_name.values()
    }
    if lean_primitive_types != expected_primitive_types:
        raise ValueError('Lean Primitive.type differs from the C builtin signatures: '
                         f'Lean={lean_primitive_types!r}, expected={expected_primitive_types!r}')

    # The C table order also assigns the runtime builtin identities. Check it
    # against the Lean identity environment and its name-to-primitive map so
    # drift in either independently maintained table is caught here.
    identity_start = binding_walk.find('def builtinEnvironment : Environment :=')
    identity_end = binding_walk.find('theorem builtinEnvironment_floatArithmetic_ids', identity_start)
    primitive_start = binding_walk.find('def builtinPrimitive :', identity_end)
    primitive_end = binding_walk.find('theorem builtinEnvironment_primitiveRows', primitive_start)
    if min(identity_start, identity_end, primitive_start, primitive_end) < 0:
        raise ValueError('Lean builtin identity/primitive tables were not found')
    identity_block = binding_walk[identity_start:identity_end]
    lean_names = re.findall(r'"([^"\n]+)"', identity_block)
    primitive_block = binding_walk[primitive_start:primitive_end]
    lean_primitives = dict(re.findall(
        r'\|\s*"([^"\n]+)"\s*=>\s*some\s+\.([A-Za-z][A-Za-z0-9]*)',
        primitive_block))
    if lean_names != [name for name, *_rest in rows]:
        raise ValueError('C builtin registration order differs from Lean identity order: '
                         f'C={[name for name, *_rest in rows]!r}, Lean={lean_names!r}')
    if lean_primitives != {name: entry[0] for name, entry in primitive_by_name.items()}:
        raise ValueError('Lean builtin name-to-primitive table differs from exporter table')
    for theorem in ('builtinEnvironment_all_ids',
                    'builtinEnvironment_primitiveRows',
                    'builtinEnvironment_primitiveTypeRows',
                    'builtinStringOperations_CText_semantics',
                    'builtinCharacterEquality_semantics'):
        if f'theorem {theorem}' not in binding_walk:
            raise ValueError(f'Lean 26-builtin identity/type row theorem is missing: {theorem}')
    builtin_semantics = (root / 'NLisp/BuiltinSemantics.lean').read_text(encoding='utf-8')
    string_semantics = (root / 'NLisp/BuiltinStringSemantics.lean').read_text(encoding='utf-8')
    for theorem in ('cBuiltin_toFloat_GlobalIR_semantics',
                    'cBuiltin_floatTruncate_GlobalIR_bit_model',
                    'cBuiltin_booleanEquality_GlobalIR_semantics',
                    'cBuiltin_booleanNot_GlobalIR_semantics',
                    'cBuiltin_floatComparison_GlobalIR_semantics',
                    'cBuiltin_floatComparison_fault_order',
                    'cBuiltin_floatComparison_success_preserves_type',
                    'cBuiltin_floatComparison_contextual_runtime_type_safety',
                    'cBuiltin_integerOptional_GlobalIR_semantics',
                    'cBuiltin_integerOptional_success_preserves_type',
                    'cBuiltin_integerOptional_fault_order',
                    'cBuiltin_floatBin_GlobalIR_semantics',
                    'cBuiltin_floatBin_contextual_runtime_type_safety',
                    'cBuiltin_floatBin_fault_order',
                    'cBuiltin_add_GlobalIR_semantics',
                    'cBuiltin_sub_GlobalIR_semantics',
                    'cBuiltin_mul_GlobalIR_semantics',
                    'cBuiltin_le_GlobalIR_semantics',
                    'cBuiltin_intEq_GlobalIR_semantics',
                    'cBuiltin_integerComparison_semantics',
                    'evaluateIntegerComparisonCall_success_preserves_type',
                    'evaluateIntegerComparisonCall_error_iff',
                    'evaluateStringBuiltin_error_iff',
                    'evaluateStringBuiltin_success_iff',
                    'evaluateStringBuiltin_success_preserves_type',
                    'cBuiltin_string_success_preserves_type',
                    'evaluateStringBuiltin_CText_semantics',
                    'evaluateStringBuiltin_append_CText',
                    'evaluateStringBuiltin_append_preserves_CText_wellFormed',
                    'evaluateStringBuiltin_append_embeddedNul',
                    'evaluateStringBuiltin_equal_CText',
                    'evaluateStringBuiltin_equal_embeddedNul_not_prefix',
                    'evaluateCharacterEquality_error_iff',
                    'evaluateCharacterEquality_success_iff',
                    'cBuiltin_characterEquality_success_preserves_type',
                    'cBuiltin_characterEquality_GlobalIR_semantics'):
        proof_source = string_semantics if theorem in (
            'evaluateStringBuiltin_append_CText',
            'evaluateStringBuiltin_append_preserves_CText_wellFormed',
            'evaluateStringBuiltin_append_embeddedNul',
            'evaluateStringBuiltin_equal_CText',
            'evaluateStringBuiltin_equal_embeddedNul_not_prefix') else builtin_semantics
        if f'theorem {theorem}' not in proof_source:
            raise ValueError(f'Lean integer builtin/GlobalIR bridge is missing: {theorem}')
    global_ir_semantics = (root / 'NLisp/GlobalIR.lean').read_text(encoding='utf-8')
    for theorem in ('FloatComparisonOperation.evaluate_left_nan',
                    'FloatComparisonOperation.evaluate_right_nan',
                    'FloatComparisonOperation.evaluate_of_not_nan',
                    'FloatComparisonOperation.runtimeValue_nan'):
        if f'theorem {theorem}' not in global_ir_semantics:
            raise ValueError(f'Lean Float comparison NaN contract is missing: {theorem}')
    comparison_start = global_ir_semantics.find('def FloatComparisonOperation.evaluate')
    comparison_end = global_ir_semantics.find('\ndef floatComparisonRuntimeValue', comparison_start)
    if comparison_start < 0 or comparison_end < 0:
        raise ValueError('Lean Float comparison evaluator was not found')
    comparison_model = global_ir_semantics[comparison_start:comparison_end]
    for branch in ('if left.isNaN || right.isNaN then false',
                   '| .lt => decide (left < right)',
                   '| .le => decide (left ≤ right)',
                   '| .gt => decide (left > right)',
                   '| .ge => decide (left ≥ right)',
                   '| .eq => left == right'):
        if branch not in comparison_model:
            raise ValueError(f'Lean Float comparison model differs from C IEEE operation: {branch}')
    if 'import NLisp.BuiltinSemantics' not in (root / 'NLisp.lean').read_text(encoding='utf-8'):
        raise ValueError('integer builtin/GlobalIR bridge is not in NLisp.lean')

    c_operation_to_primitive = {
        'BI_ADD': 'add', 'BI_SUB': 'sub', 'BI_MUL': 'mul',
        'BI_QUOTIENT': 'quotient', 'BI_REMAINDER': 'remainder',
        'BI_LT': 'lt', 'BI_LE': 'le', 'BI_GT': 'gt', 'BI_GE': 'ge',
        'BI_EQ': 'intEq', 'BI_BOOL_EQ': 'boolEq', 'BI_NOT': 'not',
        'BI_FADD': 'fadd', 'BI_FSUB': 'fsub', 'BI_FMUL': 'fmul',
        'BI_FDIV': 'fdiv', 'BI_FLT': 'flt', 'BI_FLE': 'fle',
        'BI_FGT': 'fgt', 'BI_FGE': 'fge', 'BI_FEQ': 'floatEq',
        'BI_TO_FLOAT': 'toFloat', 'BI_TRUNCATE': 'truncate',
        'BI_STRING_EQ': 'stringEq', 'BI_STRING_APPEND': 'append',
        'BI_CHAR_EQ': 'charEq',
    }
    c_type_to_lean = {
        'TY_BOOL': 'Boolean', 'TY_INT': 'Integer', 'TY_FLOAT': 'Float',
        'TY_STRING': 'String', 'TY_CHAR': 'Character', 'TY_UNIT': 'Unit',
    }
    seen = set()
    for name, operation, c_input, c_output, c_arity, optional in rows:
        if name in seen:
            raise ValueError(f'duplicate C builtin name: {name}')
        seen.add(name)
        expected = primitive_by_name.get(name)
        if expected is None:
            raise ValueError(f'C builtin has no Lean exporter entry: {name}')
        primitive, input_type, output_type, arity = expected
        if operation not in c_operation_to_primitive:
            raise ValueError(f'unknown C builtin operation for {name}: {operation}')
        if c_input not in c_type_to_lean or c_output not in c_type_to_lean:
            raise ValueError(f'unknown C builtin type for {name}')
        decoded_output = c_type_to_lean[c_output]
        if optional == 'true':
            decoded_output = ('Option', decoded_output)
        actual = (c_operation_to_primitive[operation], c_type_to_lean[c_input],
                  decoded_output, int(c_arity))
        if actual != expected:
            raise ValueError(f'C/Lean builtin contract mismatch for {name}: '
                             f'C={actual!r}, Lean={expected!r}')
    if seen != set(primitive_by_name):
        missing = sorted(set(primitive_by_name) - seen)
        raise ValueError(f'Lean builtin entries missing from C table: {missing!r}')

    # Ensure every registered operation is also referenced by the executable
    # builtin dispatcher. This is a structural check, not a proof of the C
    # branch's arithmetic or Unicode semantics.
    apply_start = source.find('static Value *apply(Runtime *r, Value *f, Value **args, size_t n, Span span) {')
    eval_start = source.find('static Value *eval(Runtime *r, const SExpr *x, RBind *env) {',
                             apply_start + 1)
    if apply_start < 0 or eval_start < 0:
        raise ValueError('C builtin apply implementation was not found')
    implementation = source[apply_start:eval_start]
    implemented_operations = set(re.findall(r'\bBI_[A-Z_]+\b', implementation))
    registered_operations = {operation for _name, operation, *_rest in rows}
    missing_operations = sorted(registered_operations - implemented_operations)
    if missing_operations:
        raise ValueError(f'C builtin operations lack apply implementation references: '
                         f'{missing_operations!r}')

    # Pin each operation identity to its executable C operation, rather than
    # accepting mere mentions of every enum in the dispatcher. The patterns
    # cover the concrete integer/float operators, Option branches, conversions,
    # and length-bearing text operations represented by the Lean primitive map.
    runtime_semantics = {
        'BI_ADD': r'case\s+BI_ADD:\s*mpz_add\(v->as\.integer,\s*args\[0\]->as\.integer,\s*args\[1\]->as\.integer\)',
        'BI_SUB': r'case\s+BI_SUB:\s*mpz_sub\(v->as\.integer,\s*args\[0\]->as\.integer,\s*args\[1\]->as\.integer\)',
        'BI_MUL': r'case\s+BI_MUL:\s*mpz_mul\(v->as\.integer,\s*args\[0\]->as\.integer,\s*args\[1\]->as\.integer\)',
        'BI_QUOTIENT': r'mpz_tdiv_q\(v->as\.some->as\.integer,\s*args\[0\]->as\.integer,\s*args\[1\]->as\.integer\)',
        'BI_REMAINDER': r'mpz_tdiv_r\(v->as\.some->as\.integer,\s*args\[0\]->as\.integer,\s*args\[1\]->as\.integer\)',
        'BI_LT': r'case\s+BI_LT:\s*v->as\.boolean\s*=\s*comparison\s*<\s*0',
        'BI_LE': r'case\s+BI_LE:\s*v->as\.boolean\s*=\s*comparison\s*<=\s*0',
        'BI_GT': r'case\s+BI_GT:\s*v->as\.boolean\s*=\s*comparison\s*>\s*0',
        'BI_GE': r'case\s+BI_GE:\s*v->as\.boolean\s*=\s*comparison\s*>=\s*0',
        'BI_EQ': r'comparison\s*==\s*0',
        'BI_BOOL_EQ': r'args\[0\]->as\.boolean\s*==\s*args\[1\]->as\.boolean',
        'BI_NOT': r'arity\s*==\s*1U\s*\?\s*!args\[0\]->as\.boolean',
        'BI_FADD': r'case\s+BI_FADD:\s*v->as\.floating\s*=\s*left\s*\+\s*right',
        'BI_FSUB': r'case\s+BI_FSUB:\s*v->as\.floating\s*=\s*left\s*-\s*right',
        'BI_FMUL': r'case\s+BI_FMUL:\s*v->as\.floating\s*=\s*left\s*\*\s*right',
        'BI_FDIV': r'case\s+BI_FDIV:\s*v->as\.floating\s*=\s*left\s*/\s*right',
        'BI_FLT': r'case\s+BI_FLT:\s*v->as\.boolean\s*=\s*left\s*<\s*right',
        'BI_FLE': r'case\s+BI_FLE:\s*v->as\.boolean\s*=\s*left\s*<=\s*right',
        'BI_FGT': r'case\s+BI_FGT:\s*v->as\.boolean\s*=\s*left\s*>\s*right',
        'BI_FGE': r'case\s+BI_FGE:\s*v->as\.boolean\s*=\s*left\s*>=\s*right',
        'BI_FEQ': r'default:\s*v->as\.boolean\s*=\s*left\s*==\s*right',
        'BI_TO_FLOAT': r'v->as\.floating\s*=\s*integer_to_float\(args\[0\]->as\.integer\)',
        'BI_TRUNCATE': r'isfinite\(input\).*?mpz_set_d\(v->as\.some->as\.integer,\s*input\)',
        'BI_STRING_EQ': r'args\[0\]->as\.text\.length\s*==\s*args\[1\]->as\.text\.length\s*&&\s*memcmp\(args\[0\]->as\.text\.data,\s*args\[1\]->as\.text\.data,\s*args\[0\]->as\.text\.length\)\s*==\s*0',
        'BI_STRING_APPEND': r'v->as\.text\.length\s*=\s*left\.length\s*\+\s*right\.length.*?memcpy\(v->as\.text\.data,\s*left\.data,\s*left\.length\).*?memcpy\(v->as\.text\.data\s*\+\s*left\.length,\s*right\.data,\s*right\.length\)',
        'BI_CHAR_EQ': r'args\[0\]->as\.character\s*==\s*args\[1\]->as\.character',
    }
    for operation, pattern in runtime_semantics.items():
        if operation not in registered_operations:
            raise ValueError(f'C builtin semantic contract has no registration: {operation}')
        if re.search(pattern, implementation, flags=re.S) is None:
            raise ValueError(f'C builtin operation does not match its runtime contract: {operation}')

    integer_comparison_start = builtin_semantics.find(
        'def IntegerComparisonOperation.evaluate')
    integer_comparison_end = builtin_semantics.find(
        '\ndef evaluateIntegerComparisonCall', integer_comparison_start)
    if integer_comparison_start < 0 or integer_comparison_end < 0:
        raise ValueError('Lean integer comparison operation model was not found')
    integer_comparison_model = builtin_semantics[integer_comparison_start:integer_comparison_end]
    for branch in ('| .lt => decide (left < right)', '| .le => decide (left ≤ right)',
                   '| .gt => decide (left > right)', '| .ge => decide (left ≥ right)'):
        if branch not in integer_comparison_model:
            raise ValueError(f'Lean integer comparison model differs from C: {branch}')
    if re.search(
            r'int\s+comparison\s*=\s*mpz_cmp\(args\[0\]->as\.integer,\s*'
            r'args\[1\]->as\.integer\)\s*;', implementation) is None:
        raise ValueError('C integer comparisons no longer use mpz_cmp on both arguments')

    conversion_start = source.find('static double integer_to_float(const mpz_t value) {')
    conversion_end = source.find('\nstatic Value *eval(', conversion_start + 1)
    if conversion_start < 0 or conversion_end < 0:
        raise ValueError('C integer_to_float implementation was not found')
    conversion = source[conversion_start:conversion_end]
    for pattern, description in (
            (r'mpz_sizeinbase\(magnitude,\s*2\)', 'integer magnitude bit length'),
            (r'bits\s*<=\s*53U.*?mpz_get_d\(value\)', 'exact significand fast path'),
            (r'bits\s*>\s*1024U.*?INFINITY', 'overflow to signed infinity'),
            (r'mpz_fdiv_q_2exp\(significand,\s*magnitude,\s*\(mp_bitcnt_t\)shift\)',
             '53-bit significand extraction'),
            (r'mpz_tstbit\(magnitude,\s*\(mp_bitcnt_t\)\(shift\s*-\s*1U\)\)',
             'round-to-nearest midpoint test'),
            (r'mpz_scan1\(magnitude,\s*0U\)\s*<\s*shift\s*-\s*1U\s*\|\|\s*mpz_odd_p\(significand\)',
             'ties-to-even decision'),
            (r'ldexp\(mpz_get_d\(significand\),\s*\(int\)shift\)',
             'rounded binary64 scaling')):
        if re.search(pattern, conversion, flags=re.S) is None:
            raise ValueError(f'C integer_to_float rounding contract missing: {description}')

    # The C text operations use explicit UTF-8 byte lengths. Require the Lean
    # model that identifies byte equality with String equality and byte
    # concatenation with String append, so table validation also checks the
    # semantic bridge needed by BI_STRING_EQ and BI_STRING_APPEND.
    lexical_source = (root / 'NLisp/Lexical.lean').read_text(encoding='utf-8')
    for theorem in ('CTextModel.stringEqual_ofString_iff',
                    'CTextModel.stringAppend_ofString',
                    'CTextModel.stringAppend_byteLength',
                    'CTextModel.stringAppend_assoc',
                    'CTextModel.stringAppend_empty',
                    'CTextModel.decode_ofString',
                    'CTextModel.decode_stringAppend_ofString',
                    'CTextModel.stringEqual_after_append_iff',
                    'CTextModel.ofString_wellFormed',
                    'CTextModel.stringAppend_preserves_wellFormed',
                    'CTextModel.decode_wellFormed',
                    'CTextModel.embeddedNul_append_is_lengthBearing',
                    'CTextModel.stringEqual_embeddedNul_not_prefix',
                    'readStringLiteral_cText_wellFormed',
                    'readStringLiteral_cText_decodes_exactly'):
        if f'theorem {theorem}' not in lexical_source:
            raise ValueError(f'Lean C text builtin correspondence is missing: {theorem}')

    dispatch_contracts = (
        (r'if\s*\(f->as\.builtin\s*==\s*BI_STRING_EQ\s*\|\|\s*'
         r'f->as\.builtin\s*==\s*BI_STRING_APPEND\s*\|\|\s*'
         r'f->as\.builtin\s*==\s*BI_CHAR_EQ\)\s*\{.*?'
         r'if\s*\(n\s*!=\s*2U\s*\|\|\s*args\[0\]->kind\s*!=\s*expected\s*\|\|\s*'
         r'args\[1\]->kind\s*!=\s*expected\)',
         'string and character builtins require two operands of the selected runtime kind'),
        (r'if\s*\(f->as\.builtin\s*==\s*BI_STRING_APPEND\)\s*\{.*?'
         r'if\s*\(left\.length\s*>\s*SIZE_MAX\s*-\s*right\.length\s*-\s*1U\).*?'
         r'fail\(r->e,\s*NLISP_RUNTIME_ERROR,.*?String size overflow.*?'
         r'v\s*=\s*vnew\(r,\s*V_STRING\).*?'
         r'memcpy\(v->as\.text\.data,\s*left\.data,\s*left\.length\).*?'
         r'memcpy\(v->as\.text\.data\s*\+\s*left\.length,\s*right\.data,\s*right\.length\)',
         'string append checks size overflow and returns concatenated String bytes'),
        (r'v\s*=\s*vnew\(r,\s*V_BOOL\)\s*;\s*'
         r'v->as\.boolean\s*=\s*expected\s*==\s*V_CHAR\s*\?\s*'
         r'args\[0\]->as\.character\s*==\s*args\[1\]->as\.character\s*:\s*'
         r'args\[0\]->as\.text\.length\s*==\s*args\[1\]->as\.text\.length',
         'text and character equality return Boolean using scalar or byte equality'),
        (r'if\s*\(f->as\.builtin\s*==\s*BI_TO_FLOAT\)\s*\{\s*'
         r'if\s*\(n\s*!=\s*1U\s*\|\|\s*args\[0\]->kind\s*!=\s*V_INT\)',
         'to-float requires one Integer operand'),
        (r'if\s*\(f->as\.builtin\s*==\s*BI_TO_FLOAT\)\s*\{.*?'
         r'v\s*=\s*vnew\(r,\s*V_FLOAT\).*?'
         r'v->as\.floating\s*=\s*integer_to_float\(args\[0\]->as\.integer\)',
         'to-float returns a Float produced by integer_to_float'),
        (r'if\s*\(f->as\.builtin\s*==\s*BI_TRUNCATE\)\s*\{.*?'
         r'if\s*\(n\s*!=\s*1U\s*\|\|\s*args\[0\]->kind\s*!=\s*V_FLOAT\)',
         'float-truncate requires one Float operand'),
        (r'if\s*\(f->as\.builtin\s*==\s*BI_TRUNCATE\)\s*\{.*?'
         r'if\s*\(!isfinite\(input\)\)\s*return\s+vnew\(r,\s*V_NONE\)\s*;\s*'
         r'v\s*=\s*vnew\(r,\s*V_SOME\)\s*;\s*'
         r'v->as\.some\s*=\s*vnew\(r,\s*V_INT\)\s*;\s*'
         r'mpz_set_d\(v->as\.some->as\.integer,\s*input\)',
         'float-truncate returns None for non-finite inputs and Some Integer otherwise'),
        (r'if\s*\(f->as\.builtin\s*>=\s*BI_FADD\s*&&\s*'
         r'f->as\.builtin\s*<=\s*BI_FEQ\)\s*\{.*?'
         r'if\s*\(n\s*!=\s*2U\s*\|\|\s*args\[0\]->kind\s*!=\s*V_FLOAT\s*\|\|\s*'
         r'args\[1\]->kind\s*!=\s*V_FLOAT\).*?'
         r'v\s*=\s*vnew\(r,\s*f->as\.builtin\s*<=\s*BI_FDIV\s*\?\s*V_FLOAT\s*:\s*V_BOOL\)',
         'Float operations require Float operands and select Float/Boolean results by operation'),
        (r'if\s*\(f->as\.builtin\s*==\s*BI_NOT\s*\|\|\s*'
         r'f->as\.builtin\s*==\s*BI_BOOL_EQ\)\s*\{.*?'
         r'if\s*\(n\s*!=\s*arity\s*\|\|\s*args\[0\]->kind\s*!=\s*V_BOOL\s*\|\|\s*'
         r'\(arity\s*==\s*2U\s*&&\s*args\[1\]->kind\s*!=\s*V_BOOL\)\).*?'
         r'v\s*=\s*vnew\(r,\s*V_BOOL\)',
         'Boolean operations enforce unary/binary arity and Boolean results'),
        (r'if\s*\(n\s*!=\s*2U\s*\|\|\s*args\[0\]->kind\s*!=\s*V_INT\s*\|\|\s*'
         r'args\[1\]->kind\s*!=\s*V_INT\)',
         'integer operations require two Integer operands'),
        (r'if\s*\(f->as\.builtin\s*>=\s*BI_LT\s*&&\s*'
         r'f->as\.builtin\s*<=\s*BI_EQ\)\s*\{.*?'
         r'v\s*=\s*vnew\(r,\s*V_BOOL\).*?switch\s*\(f->as\.builtin\)',
         'integer comparisons and equality return Boolean'),
        (r'v\s*=\s*vnew\(r,\s*V_INT\)\s*;\s*'
         r'switch\s*\(f->as\.builtin\)\s*\{\s*'
         r'case\s+BI_ADD:.*?case\s+BI_SUB:.*?case\s+BI_MUL:',
         'integer arithmetic allocates Integer results for add/subtract/multiply'),
        (r'if\s*\(f->as\.builtin\s*==\s*BI_QUOTIENT\s*\|\|\s*'
         r'f->as\.builtin\s*==\s*BI_REMAINDER\)\s*\{\s*'
         r'if\s*\(mpz_sgn\(args\[1\]->as\.integer\)\s*==\s*0\)\s*'
         r'return\s+vnew\(r,\s*V_NONE\)',
         'quotient and remainder map zero divisors to None'),
    )
    for pattern, description in dispatch_contracts:
        if re.search(pattern, implementation, flags=re.S) is None:
            raise ValueError(f'C builtin dispatch contract missing: {description}')


def verify_c_type_argument_call_inference():
    """Pin C check_call's inference order to the Lean constraint model.

    This checks the concrete C dispatch and its use of match_type against the
    Lean state-simulation and result-substitution theorem names. It is a
    source-structure drift check, not an execution-semantics proof.
    """
    root = pathlib.Path(__file__).resolve().parents[1]
    c_source = (root / 'src/nlisp.c').read_text(encoding='utf-8')
    lean_source = (root / 'NLisp/CTypeArguments.lean').read_text(encoding='utf-8')
    inference_source = (root / 'NLisp/CTypeArgumentInference.lean').read_text(encoding='utf-8')
    type_arguments_source = (root / 'NLisp/TypeArguments.lean').read_text(encoding='utf-8')
    monotype_decode_contracts = (
        'decodeCType_success_is_monotype',
        'decodeCTypes_success_are_monotypes',
    )
    for theorem in monotype_decode_contracts:
        if re.search(rf'\btheorem\s+{theorem}\b', lean_source) is None:
            raise ValueError(f'C decoded monotype contract missing: {theorem}')
    start = c_source.find('static Type *check_call(Arena *a, const SExpr *x, TBind *env, Error *e) {')
    end = c_source.find('\nstatic Type *check_expr_inner(', start + 1)
    if start < 0 or end < 0:
        raise ValueError('C check_call implementation was not found')
    body = c_source[start:end]
    contracts = (
        (r'Type\s*\*f\s*=\s*check_expr\(a,\s*x->items\[0\],\s*env,\s*e\);',
         'callee type is checked before argument inference'),
        (r'if\s*\(f->kind\s*==\s*TY_FORALL\)\s*\{\s*scheme\s*=\s*f;\s*'
         r'f\s*=\s*scheme->result;\s*sub\s*=\s*\(Type\s*\*\*\)aalloc\(a,\s*'
         r'scheme->variable_count\s*\*\s*sizeof\(\*sub\)\);\s*\}',
         'only callee quantified slots receive an inference array'),
        (r'if\s*\(f->kind\s*!=\s*TY_FUN\)',
         'non-function rejection precedes argument matching'),
        (r'if\s*\(x->count\s*-\s*1U\s*!=\s*f->arity\)',
         'arity is checked before argument traversal'),
        (r'for\s*\(i\s*=\s*0U;\s*i\s*<\s*f->arity;\s*i\+\+\)\s*\{\s*'
         r'Type\s*\*got\s*=\s*check_expr\(a,\s*x->items\[i\s*\+\s*1U\],\s*env,\s*e\);'
         r'\s*if\s*\(got\s*==\s*NULL\)\s*return\s+NULL;\s*'
         r'if\s*\(scheme\s*!=\s*NULL\)\s*\{\s*'
         r'if\s*\(!match_type\(f->params\[i\],\s*got,\s*scheme,\s*sub\)\)',
         'arguments are checked left-to-right and update shared quantified constraints'),
        (r'for\s*\(i\s*=\s*0U;\s*i\s*<\s*scheme->variable_count;\s*i\+\+\)\s*'
         r'if\s*\(sub\[i\]\s*==\s*NULL\)',
         'unassigned quantified variables reject inference after argument traversal'),
        (r'return\s+substitute_type\(a,\s*f->result,\s*scheme,\s*sub\)\s*;',
         'the inferred substitution is applied to the result type'),
    )
    for pattern, description in contracts:
        if re.search(pattern, body, flags=re.S) is None:
            raise ValueError(f'C check_call inference contract missing: {description}')
    monotype_start = c_source.find('static bool monotype(const Type *t) {')
    substitute_start = c_source.find('static Type *substitute_type(', monotype_start + 1)
    if monotype_start < 0 or substitute_start < 0:
        raise ValueError('C monotype/match_type implementation was not found')
    matcher = c_source[monotype_start:substitute_start]
    matcher_contracts = (
        (r'if\s*\(t->kind\s*==\s*TY_FORALL\)\s*return\s+false\s*;',
         'polymorphic actual argument types are rejected'),
        (r'if\s*\(t->kind\s*==\s*TY_LIST\s*\|\|\s*t->kind\s*==\s*TY_OPTION\)\s*'
         r'return\s+monotype\(t->elem\)\s*;',
         'List and Option actual types are recursively checked for monomorphism'),
        (r'for\s*\(i\s*=\s*0U;\s*i\s*<\s*t->arity;\s*i\+\+\)\s*'
         r'if\s*\(!monotype\(t->params\[i\]\)\)\s*return\s+false\s*;',
         'function argument types are recursively checked for monomorphism'),
        (r'return\s+monotype\(t->result\)\s*;',
         'function result type is recursively checked for monomorphism'),
        (r'if\s*\(pattern\s*==\s*scheme->variables\[i\]\)\s*\{\s*'
         r'if\s*\(sub\[i\]\s*==\s*NULL\)\s*\{\s*sub\[i\]\s*=\s*actual;',
         'quantified variables are assigned by scheme pointer identity'),
        (r'if\s*\(pattern->kind\s*==\s*TY_LIST\s*\|\|\s*pattern->kind\s*==\s*TY_OPTION\)\s*'
         r'return\s+match_type\(pattern->elem,\s*actual->elem,\s*scheme,\s*sub\)\s*;',
         'List and Option constraints recurse into the element type'),
        (r'if\s*\(pattern->arity\s*!=\s*actual->arity\)\s*return\s+false\s*;',
         'function type constraints require matching arity'),
        (r'if\s*\(!match_type\(pattern->params\[i\],\s*actual->params\[i\],\s*scheme,\s*sub\)\)\s*'
         r'return\s+false\s*;',
         'function parameter constraints recurse left-to-right'),
        (r'return\s+match_type\(pattern->result,\s*actual->result,\s*scheme,\s*sub\)\s*;',
         'function result constraint recurses after parameter constraints'),
    )
    for pattern, description in matcher_contracts:
        if re.search(pattern, matcher, flags=re.S) is None:
            raise ValueError(f'C match_type inference contract missing: {description}')
    for theorem in (
            'decodeCType_injective',
            'cTypeEq_complete_of_decoded_equal',
            'cMatchType_and_types_state_simulation',
            'cMatchTypes_and_collectArguments_reject_arity_mismatch',
            'cMonotype',
            'cMatchTypes_success_infers_arguments_and_substitutes_result',
            'cMatchTypes_success_infers_arguments_and_substitutes_result_of_decoded_actuals',
            'cMatchTypes_success_substitutes_result_like_Lean_from_empty',
            'cMatchType_list_atomic_state_simulation_reverse_of_monotype',
            'cMatchType_option_atomic_state_simulation_reverse_of_monotype',
            'cMatchType_wrappedAtomic_state_simulation_reverse_of_monotype',
            'cMatchType_function_state_simulation_reverse_of_decoded_parameters',
            'cMatchType_nullaryFunction_atomicResult_state_simulation_reverse',
            'cMatchType_unaryFunction_atomic_state_simulation_reverse',
            'cMatchType_function_atomicParameters_primitiveActuals_state_simulation_reverse',
            'cMatchTypes_atomicMonotypeRows_state_simulation_reverse',
            'cMatchType_function_atomicParameters_monotypeActuals_state_simulation_reverse',
            'cMatchType_unaryFunction_wrappedAtomicParameter_state_simulation_reverse',
            'cMatchTypes_wrappedAtomicMonotypeRows_state_simulation_reverse',
            'cMatchType_function_wrappedAtomicMonotypeRows_state_simulation_reverse',
            'cMatchType_function_wrappedAtomicMonotypeRowsResult_state_simulation_reverse',
            'cMatchTypes_state_simulation_reverse_of_steps',
            'collectArguments_success_requires_fuel',
            'cMatchTypes_state_simulation_reverse_of_steps_from_success',
            'collectArguments_state_simulation_reverse_of_steps_decoded',
            'cMatchTypes_arity_mismatch'):
        if f'theorem {theorem}' not in lean_source:
            raise ValueError(f'Lean C/Lean call inference theorem missing: {theorem}')
    complete_start = lean_source.find('theorem cTypeEq_complete_of_decoded_equal')
    complete_end = lean_source.find('\n/--', complete_start + 1)
    complete_proof = lean_source[complete_start:complete_end if complete_end >= 0 else None]
    if complete_start < 0 or any(dependency not in complete_proof for dependency in (
            'decodeCType_injective', 'cTypeEq_same_node_of_cost')):
        raise ValueError('decoded-equality C comparison completeness proof is incomplete')
    call_theorem = 'theorem cCheckCall_success_agrees_with_inferTypeArguments'
    if 'theorem inferTypeArguments_success_collectArguments' not in type_arguments_source:
        raise ValueError('Lean successful inference collector extraction theorem is missing')
    if 'theorem typeArgumentSolution_cMatchTypes_atomicRows' not in inference_source:
        raise ValueError('Lean solution-level reverse C matcher simulation is missing')
    if 'theorem typeArgumentSolution_cMatchTypes_wrappedAtomicRows' not in inference_source:
        raise ValueError('Lean wrapped-atomic reverse C matcher simulation is missing')
    if 'theorem typeArgumentSolution_cMatchTypes_function_wrappedAtomic' not in inference_source:
        raise ValueError('Lean function-argument reverse C matcher simulation is missing')
    if 'theorem typeArgumentSolution_cMatchTypes_functionRows' not in inference_source:
        raise ValueError('Lean multi-function-argument reverse C matcher simulation is missing')
    call_start = inference_source.find(call_theorem)
    if call_start < 0:
        raise ValueError('Lean successful check_call inference/result theorem is missing')
    call_end = inference_source.find('\nend NLisp.Surface', call_start)
    call_body = inference_source[call_start:call_end if call_end >= 0 else None]
    for theorem in (
            'cMatchTypes_success_agrees_with_inferTypeArguments',
            'cMatchTypes_success_agrees_with_inferTypeArguments_of_all_slots',
            'cMatchTypes_monomorphic_success_agrees_with_inferTypeArguments',
            'cCheckCall_success_agrees_with_inferTypeArguments',
            'cCheckCall_success_resultWellFormed'):
        declaration_start = inference_source.find(f'theorem {theorem}')
        declaration_end = inference_source.find(' := by', declaration_start)
        if declaration_start < 0 or declaration_end < 0:
            raise ValueError(f'Lean C-call theorem declaration is missing: {theorem}')
        declaration = inference_source[declaration_start:declaration_end]
        if 'actualsMonotype' in declaration:
            raise ValueError(
                f'{theorem} still assumes monotype independently of successful decoding')
        if theorem == 'cCheckCall_success_agrees_with_inferTypeArguments':
            for contract in ('matched : cMatchTypes', 'allAssigned :',
                             'resultDecoded : decodeCType',
                             'patterns.length = actuals.length'):
                if contract not in declaration:
                    raise ValueError(f'{theorem} omits check_call contract: {contract}')
        if theorem == 'cCheckCall_success_resultWellFormed':
            for contract in ('resultWellFormed :', 'matched : cMatchTypes',
                             'allAssigned :', 'resultDecoded : decodeCType',
                             '.wellFormed callerPointers.length'):
                if contract not in declaration:
                    raise ValueError(f'{theorem} omits substituted-result contract: {contract}')
    result_wf_start = inference_source.find('theorem cCheckCall_success_resultWellFormed')
    result_wf_end = inference_source.find('\n/-- ', result_wf_start + 1)
    result_wf_body = inference_source[result_wf_start:result_wf_end]
    if 'cCheckCall_success_agrees_with_inferTypeArguments' not in result_wf_body or \
            'solution.instantiated_result_wellFormed' not in result_wf_body:
        raise ValueError('C check_call result scope theorem no longer composes inference with substitution safety')
    for dependency, description in (
            ('cMatchTypes_arity_mismatch', 'matcher success establishes C arity acceptance'),
            ('cMatchTypes_success_agrees_with_inferTypeArguments_of_all_slots',
             'complete C slot assignment establishes Lean inference and result substitution')):
        if dependency not in call_body:
            raise ValueError(f'Lean successful check_call theorem omits {description}')


def verify_integer_division_semantics():
    """Pin the C/GMP quotient and remainder branch to Lean's signed model.

    This is a source-structure drift check. The Lean theorems establish the
    signed model's algebraic contract; this check ensures C still dispatches
    zero divisors to None and calls GMP's truncating quotient/remainder APIs.
    It does not claim a machine-checked proof of GMP or C execution semantics.
    """
    root = pathlib.Path(__file__).resolve().parents[1]
    c_source = (root / 'src/nlisp.c').read_text(encoding='utf-8')
    lean_source = (root / 'NLisp/TypedExpansion.lean').read_text(encoding='utf-8')
    start = c_source.find('if (f->as.builtin == BI_QUOTIENT || f->as.builtin == BI_REMAINDER) {')
    end = c_source.find('\n        if (f->as.builtin >= BI_LT', start + 1)
    if start < 0 or end < 0:
        raise ValueError('C quotient/remainder builtin branch was not found')
    branch = c_source[start:end]
    apply_start = c_source.rfind(
        'static Value *apply(Runtime *r, Value *f, Value **args, size_t n, Span span) {',
        0, start)
    if apply_start < 0:
        raise ValueError('C builtin apply function was not found before quotient/remainder branch')
    before_branch = c_source[apply_start:start]
    if re.search(
            r'n\s*!=\s*2U\s*\|\|\s*args\[0\]->kind\s*!=\s*V_INT\s*\|\|\s*'
            r'args\[1\]->kind\s*!=\s*V_INT', before_branch, flags=re.S) is None:
        raise ValueError('C quotient/remainder dispatch no longer follows arity and Integer shape checks')
    c_contract = (
        (r'mpz_sgn\(args\[1\]->as\.integer\)\s*==\s*0',
         'zero divisor is detected'),
        (r'return\s+vnew\(r,\s*V_NONE\)', 'zero divisor returns None'),
        (r'v\s*=\s*vnew\(r,\s*V_SOME\)', 'nonzero result is Some'),
        (r'v->as\.some\s*=\s*vnew\(r,\s*V_INT\)', 'Some payload is an Integer'),
        (r'if\s*\(f->as\.builtin\s*==\s*BI_QUOTIENT\)\s*'
         r'mpz_tdiv_q\(v->as\.some->as\.integer,\s*args\[0\]->as\.integer,\s*'
         r'args\[1\]->as\.integer\)', 'quotient uses mpz_tdiv_q'),
        (r'else\s*mpz_tdiv_r\(v->as\.some->as\.integer,\s*args\[0\]->as\.integer,\s*'
         r'args\[1\]->as\.integer\)', 'remainder uses mpz_tdiv_r'),
        (r'return\s+v\s*;', 'the constructed Option is returned'),
    )
    for pattern, description in c_contract:
        if re.search(pattern, branch, flags=re.S) is None:
            raise ValueError(f'C quotient/remainder contract missing: {description}')

    # Float truncation is another Option Integer builtin. Keep its C-side
    # failure and success cases pinned while its arbitrary-precision Lean
    # semantics are still being developed.
    truncate_start = c_source.find(
        'if (f->as.builtin == BI_TRUNCATE) {', apply_start)
    truncate_end = c_source.find('\n        if (f->as.builtin >= BI_FADD', truncate_start + 1)
    if truncate_start < 0 or truncate_end < 0:
        raise ValueError('C float-truncate builtin branch was not found')
    truncate_branch = c_source[truncate_start:truncate_end]
    truncate_contract = (
        (r'n\s*!=\s*1U\s*\|\|\s*args\[0\]->kind\s*!=\s*V_FLOAT',
         'float-truncate checks unary Float input'),
        (r'input\s*=\s*args\[0\]->as\.floating',
         'float-truncate reads its Float argument'),
        (r'!isfinite\(input\)\s*\)\s*return\s+vnew\(r,\s*V_NONE\)',
         'non-finite float-truncate input returns None'),
        (r'v\s*=\s*vnew\(r,\s*V_SOME\)',
         'finite float-truncate input returns Some'),
        (r'v->as\.some\s*=\s*vnew\(r,\s*V_INT\)',
         'float-truncate Some payload is Integer'),
        (r'mpz_set_d\(v->as\.some->as\.integer,\s*input\)',
         'float-truncate delegates toward-zero conversion to mpz_set_d'),
        (r'return\s+v\s*;', 'float-truncate returns its Option value'),
    )
    for pattern, description in truncate_contract:
        if re.search(pattern, truncate_branch, flags=re.S) is None:
            raise ValueError(f'C float-truncate contract missing: {description}')

    lean_contract = (
        r'def\s+truncQuotient\s*\(left right : Int\)\s*:\s*Int\s*:=\s*'
        r'let\s+magnitude\s*:=\s*Int\.ofNat\s*\(left\.natAbs\s*/\s*right\.natAbs\)\s*'
        r'if\s*\(left\s*<\s*0\)\s*=\s*\(right\s*<\s*0\)\s*then\s*magnitude\s*else\s*-magnitude'
    )
    if re.search(lean_contract, lean_source, flags=re.S) is None:
        raise ValueError('Lean truncating quotient model no longer matches signed magnitude division')
    for declaration in (
        'def integerOptional ', 'theorem truncQuotient_natAbs ',
        'theorem truncQuotient_ofNat_negSucc ', 'theorem truncQuotient_negSucc_ofNat ',
        'theorem truncQuotient_negSucc_negSucc ', 'theorem truncRemainder_sign ',
        'theorem truncRemainder_natAbs_lt ', 'theorem integerOptional_remainder_abs_bound ',
    ):
        if declaration not in lean_source:
            raise ValueError(f'Lean quotient/remainder specification missing: {declaration.strip()}')
    if not re.search(
            r'\.quotient\s*=>\s*some\s*\(truncQuotient\s+left\s+right\).*?'
            r'\.remainder\s*=>\s*some\s*\(left\s*-\s*truncQuotient\s+left\s+right\s*\*\s*right\)',
            lean_source, flags=re.S):
        raise ValueError('Lean Option quotient/remainder equations drifted from C branch contract')

    # Keep the verified arithmetic model connected to the executable Lean
    # evaluator path as well as to the C/GMP source branch above. These checks
    # are intentionally structural: the propositions are proved by Lean in
    # IntegerOptionalCorrespondence.lean, while this prevents a future edit
    # from silently leaving those proofs out of the implementation path.
    global_ir = (root / 'NLisp/GlobalIR.lean').read_text(encoding='utf-8')
    correspondence = (root / 'NLisp/IntegerOptionalCorrespondence.lean').read_text(
        encoding='utf-8')
    for declaration in (
            'inductive IntegerOptionalOperation',
            'def IntegerOptionalOperation.toPrimitive',
            'def evaluateIntegerOptionalCall',
            'theorem evaluateIntegerOptionalCall_of_integer_children',
            'theorem integerOptionalRuntimeValue_typed'):
        if declaration not in global_ir:
            raise ValueError(f'GlobalIR Option Integer evaluator bridge missing: {declaration}')
    for declaration in (
            'theorem integerOptionValue_toCore_matches_stepResult',
            'theorem quotientBuiltin_application_steps_shared',
            'theorem remainderBuiltin_application_steps_shared',
            'theorem integerOptionValue_toRuntime_matches_global',
            'theorem evaluateIntegerOptionalCall_matches_shared',
            'theorem evaluateIntegerOptionalCall_zero_divisor_typed',
            'theorem evaluateIntegerOptionalCall_division_equation',
            'theorem quotientBuiltin_steps_agree_with_globalIR_call',
            'theorem remainderBuiltin_steps_agree_with_globalIR_call'):
        if declaration not in correspondence:
            raise ValueError(f'Lean Option Integer correspondence theorem missing: {declaration}')
    for operation, primitive in (('quotient', '.quotient'), ('remainder', '.remainder')):
        if re.search(rf'\.{operation}\s*=>\s*{re.escape(primitive)}', global_ir) is None:
            raise ValueError(f'GlobalIR {operation} operation no longer maps to its typed primitive')
    if not re.search(
            r'\{"quotient",\s*BI_QUOTIENT,\s*TY_INT,\s*TY_INT,\s*2U,\s*true\}',
            c_source):
        raise ValueError('C quotient registration no longer declares Integer -> Integer -> Option Integer')
    if not re.search(
            r'\{"remainder",\s*BI_REMAINDER,\s*TY_INT,\s*TY_INT,\s*2U,\s*true\}',
            c_source):
        raise ValueError('C remainder registration no longer declares Integer -> Integer -> Option Integer')

    for declaration in (
            'def binary64Exponent ', 'def binary64Fraction ', 'def binary64Truncate ',
            'theorem binary64Truncate_nonfinite ',
            'theorem binary64Truncate_respects_sign',
            'theorem binary64Truncate_signed_zero ',
            'theorem binary64Truncate_magnitude_below_one ',
            'theorem binary64Truncate_one_bits ',
            'theorem binary64Truncate_negative_one_bits ',
            'theorem binary64Truncate_above_uint64_bits ',
            'theorem binary64Truncate_large_finite',
            'theorem binary64Truncate_normal_fractional',
            'theorem binary64Truncate_finite_cases',
            'theorem binary64Truncate_all_cases',
            'theorem binary64Truncate_none_iff_nonfinite'):
        if declaration not in lean_source:
            raise ValueError(f'Lean binary64 truncation model missing: {declaration}')
    all_cases_start = lean_source.find('theorem binary64Truncate_all_cases')
    all_cases_end = lean_source.find('\n/--', all_cases_start + 1)
    all_cases_body = lean_source[all_cases_start:all_cases_end if all_cases_end >= 0 else None]
    for dependency in ('binary64Truncate_nonfinite', 'binary64Truncate_finite_cases'):
        if dependency not in all_cases_body:
            raise ValueError(f'binary64 exhaustive classification omits {dependency}')
    none_iff_start = lean_source.find('theorem binary64Truncate_none_iff_nonfinite')
    none_iff_end = lean_source.find('\n/--', none_iff_start + 1)
    none_iff_body = lean_source[none_iff_start:none_iff_end if none_iff_end >= 0 else None]
    for dependency in ('binary64Truncate_all_cases', 'binary64Truncate_nonfinite'):
        if dependency not in none_iff_body:
            raise ValueError(f'binary64 rejection equivalence omits {dependency}')
    for field_contract in (
            r'bits\.toNat\s*/\s*2\^52\s*%\s*2\^11',
            r'bits\.toNat\s*%\s*2\^52',
            r'exponent\s*=\s*2\^11\s*-\s*1',
            r'significand\s*\*\s*2\^\(exponent\s*-\s*1075\)',
            r'significand\s*/\s*2\^\(1075\s*-\s*exponent\)'):
        if re.search(field_contract, lean_source) is None:
            raise ValueError(f'Lean binary64 truncation bit-field contract missing: {field_contract}')

    # Keep the existing evaluator-level Option result and Core bridge visible
    # to the checker. This is deliberately a structural connection check: the
    # ordinary PolyIR Term syntax still represents these operations as builtin
    # calls, and this does not prove the GMP implementation itself.
    global_ir_source = (root / 'NLisp/GlobalIR.lean').read_text(encoding='utf-8')
    option_correspondence = (root / 'NLisp/IntegerOptionalCorrespondence.lean').read_text(
        encoding='utf-8')
    required_global_ir_declarations = (
        'def evaluateIntegerOptionalCall ',
        'theorem evaluateIntegerOptionalCall_success_iff',
        'theorem evaluateIntegerOptionalCall_error_iff',
        'theorem evaluateIntegerOptionalCall_preserves_type',
        'theorem evaluateIntegerOptionalCall_of_integer_children',
        'inductive ContextualGlobalIntegerOptionalCall ',
        'theorem evaluate_contextualGlobalIntegerOptionalCall_preserves_type',
    )
    for declaration in required_global_ir_declarations:
        if declaration not in global_ir_source:
            raise ValueError(f'GlobalIR Option integer evaluator contract missing: {declaration}')
    required_bridge_declarations = (
        'theorem integerOptionValue_toCore_matches_stepResult',
        'theorem quotientBuiltin_application_steps_shared',
        'theorem remainderBuiltin_application_steps_shared',
        'theorem evaluateIntegerOptionalCall_matches_shared',
        'theorem evaluateIntegerOptionalCall_zero_divisor',
        'theorem evaluateIntegerOptionalCall_zero_divisor_typed',
        'theorem evaluateIntegerOptionalCall_division_equation',
        'theorem evaluateIntegerOptionalCall_of_contextual_integer_operands',
        'theorem evaluateIntegerOptionalCall_of_contextual_global_runtime_operands',
        'theorem evaluateContextualIntegerOptionalCall_zero_divisor',
        'theorem evaluateContextualIntegerOptionalCall_division_equation',
        'theorem evaluateIntegerOptionalCall_type_safe',
        'theorem quotientBuiltin_steps_agree_with_globalIR_call',
        'theorem remainderBuiltin_steps_agree_with_globalIR_call',
    )
    for declaration in required_bridge_declarations:
        if declaration not in option_correspondence:
            raise ValueError(f'Lean Option integer evaluator bridge missing: {declaration}')
    for theorem, dependencies in (
            ('theorem quotientBuiltin_steps_agree_with_globalIR_call',
             ('quotientBuiltin_application_steps_shared',
              'evaluateIntegerOptionalCall_matches_shared')),
            ('theorem remainderBuiltin_steps_agree_with_globalIR_call',
             ('remainderBuiltin_application_steps_shared',
              'evaluateIntegerOptionalCall_matches_shared')),
            ('theorem evaluateIntegerOptionalCall_type_safe',
             ('GlobalIR.evaluateIntegerOptionalCall_success_iff',
              'GlobalIR.integerOptionalRuntimeValue_typed')),
            ('theorem evaluateContextualIntegerOptionalCall_division_equation',
             ('TypedExpansion.integerOptional_division_equation',
              'evaluateIntegerOptionalCall_matches_shared')),
            ('theorem evaluateIntegerOptionalCall_of_contextual_global_runtime_operands',
             ('GlobalIR.evaluateIntegerOptionalCall_success_iff',
              'evaluateIntegerOptionalCall_matches_shared',
              'GlobalIR.evaluate_contextualGlobalRuntimeIntegerOptionalCall_preserves_type'))):
        theorem_start = option_correspondence.find(theorem)
        theorem_end = option_correspondence.find('\n/--', theorem_start + 1)
        if theorem_start < 0:
            raise ValueError(f'Lean Option integer bridge theorem missing: {theorem}')
        theorem_body = option_correspondence[
            theorem_start:theorem_end if theorem_end >= 0 else None]
        for dependency in dependencies:
            if dependency not in theorem_body:
                raise ValueError(
                    f'{theorem} no longer composes required semantic dependency: {dependency}')
    division_theorem_start = option_correspondence.find(
        'theorem evaluateIntegerOptionalCall_division_equation')
    division_theorem_end = option_correspondence.find('\n/--', division_theorem_start + 1)
    division_theorem = option_correspondence[
        division_theorem_start:division_theorem_end if division_theorem_end >= 0 else None]
    for contract in ('quotient.natAbs', 'remainder.natAbs',
                     'quotientValueTyped', 'remainderValueTyped',
                     'truncRemainder_sign', 'truncQuotient_natAbs'):
        if contract not in division_theorem:
            raise ValueError(f'Lean GlobalIR division result omits contract: {contract}')
    aggregate_source = (root / 'NLisp.lean').read_text(encoding='utf-8')
    if 'import NLisp.IntegerOptionalCorrespondence' not in aggregate_source:
        raise ValueError('Option integer evaluator correspondence is not included in NLisp.lean')

    # The C evaluator must finish the function expression before evaluating
    # arguments, evaluate arguments in source order, and stop at the first
    # fault. Keep this relation explicit because the Lean helper classifies
    # left/right operand faults in that same order.
    eval_start = c_source.find(
        'static Value *eval(Runtime *r, const SExpr *x, RBind *env) {')
    eval_end = c_source.find('\nstatic RBind *bind_builtin(', eval_start + 1)
    if eval_start < 0 or eval_end < 0:
        raise ValueError('C eval function was not found for application fault check')
    evaluator = c_source[eval_start:eval_end]
    app_start = evaluator.find('Value *f = eval(r, x->items[0], env);')
    app_body = evaluator[app_start:] if app_start >= 0 else ''
    ordered_app_contract = (
        (r'Value\s*\*f\s*=\s*eval\(r,\s*x->items\[0\],\s*env\);',
         'function expression is evaluated first'),
        (r'if\s*\(f\s*==\s*NULL\)\s*return\s+NULL\s*;',
         'function-expression fault stops the application'),
        (r'for\s*\(i\s*=\s*0U;\s*i\s*<\s*n;\s*i\+\+\)\s*\{\s*'
         r'args\[i\]\s*=\s*eval\(r,\s*x->items\[i\s*\+\s*1U\],\s*env\);\s*'
         r'if\s*\(args\[i\]\s*==\s*NULL\)\s*return\s+NULL;\s*\}',
         'arguments are evaluated left-to-right and the first fault stops evaluation'),
        (r'return\s+apply\(r,\s*f,\s*args,\s*n,\s*x->span\)\s*;',
         'apply runs only after all argument evaluations succeed'),
    )
    for pattern, description in ordered_app_contract:
        if re.search(pattern, app_body, flags=re.S) is None:
            raise ValueError(f'C application fault contract missing: {description}')


def verify_macro_copy_binder_composition():
    """Keep the sequential binder-copy freshness theorem in the aggregate."""
    root = pathlib.Path(__file__).resolve().parents[1]
    composition = (root / 'NLisp/CMacroCopyBinderComposition.lean').read_text(
        encoding='utf-8')
    certificate_composition = (root / 'NLisp/BinderCertificateComposition.lean').read_text(
        encoding='utf-8')
    process_certificate = (root / 'NLisp/ProcessCertificate.lean').read_text(
        encoding='utf-8')
    aggregate = (root / 'NLisp.lean').read_text(encoding='utf-8')
    if 'import NLisp.CMacroCopyBinderComposition' not in aggregate:
        raise ValueError('macro copy binder-composition proof is not in NLisp.lean')
    for declaration in (
            'theorem counterTokenChunks_eq_counterTokens',
            'theorem counterTokenChunks_unique',
            'theorem counterTokenChunks_avoid_source',
            'theorem counterTokenChunks_within_interval',
            'theorem copyBinderPhases_freshness',
            'theorem copyBinderPhases_final_counter',
            'theorem copyBinderPhases_disjoint_source'):
        if declaration not in composition:
            raise ValueError(f'macro copy binder-composition theorem missing: {declaration}')
    freshness_start = composition.find('theorem copyBinderPhases_freshness')
    freshness_end = composition.find('\n/--', freshness_start + 1)
    freshness = composition[freshness_start:freshness_end if freshness_end >= 0 else None]
    for dependency in (
            'bindingSyntaxSafe',
            'casesSyntaxSafe',
            'copyParameters_token_sequence',
            'macroCounterSafeBindingInputs_preserving',
            'macroCounterSafeCases_preserving',
            'copyBindingsWithMacros_preserving_token_sequence',
            'copyPatternWithMacros_token_sequence',
            'copyCasesWithMacros_preserving_token_sequence',
            'counterTokenChunks_unique',
            'counterTokenChunks_avoid_source',
            'counterTokenChunks_within_interval'):
        if dependency not in freshness:
            raise ValueError(f'composed binder freshness omits phase guarantee: {dependency}')
    final_counter_start = composition.find('theorem copyBinderPhases_final_counter')
    final_counter_end = composition.find('\n/--', final_counter_start + 1)
    final_counter = composition[
        final_counter_start:final_counter_end if final_counter_end >= 0 else None]
    for dependency in ('copyParameters_counter',
                       'bindingSyntaxSafe',
                       'casesSyntaxSafe',
                       'macroCounterSafeBindingInputs_preserving',
                       'macroCounterSafeCases_preserving',
                       'copyBindingsWithMacros_preserving_counter',
                       'copyPatternWithMacros_counter',
                       'copyCasesWithMacros_preserving_counter'):
        if dependency not in final_counter:
            raise ValueError(f'composed binder final counter omits phase: {dependency}')
    for declaration, source in (
            ('structure CertifiedBinderTokenChunk', certificate_composition),
            ('theorem certifiedBinderTokenChunks_pairwise_disjoint', certificate_composition),
            ('theorem certifiedBinderTokenChunks_freshness', certificate_composition),
            ('theorem checked_process_finite_binder_freshness', process_certificate)):
        if declaration not in source:
            raise ValueError(f'finite certified binder freshness connection missing: {declaration}')
    phase_record_start = certificate_composition.find('structure BinderPhaseCopy')
    phase_record_end = certificate_composition.find('\ndef BinderPhaseCopy.tokens', phase_record_start + 1)
    phase_record = certificate_composition[
        phase_record_start:phase_record_end if phase_record_end >= 0 else None]
    if phase_record_start < 0 or any(field not in phase_record for field in (
            'bindingSafe : MacroCounterSafeBindingInputs',
            'casesSafe : MacroCounterSafeCases')):
        raise ValueError('binder phase aggregate still requires semantic counter preservation')
    aggregate_start = certificate_composition.find('theorem certifiedBinderTokenChunks_freshness')
    aggregate_end = certificate_composition.find('\n/--', aggregate_start + 1)
    aggregate_proof = certificate_composition[
        aggregate_start:aggregate_end if aggregate_end >= 0 else None]
    for dependency in ('certifiedBinderTokenChunks_pairwise_disjoint',
                       'pairwiseTokenDisjoint_flatMap_unique',
                       'binderTokenSequence_avoids_source_class',
                       'binderTokenSequence_within_interval'):
        if dependency not in aggregate_proof:
            raise ValueError(f'aggregate binder freshness omits component: {dependency}')
    process_start = process_certificate.find('theorem checked_process_finite_binder_freshness')
    process_end = process_certificate.find('\n/--', process_start + 1)
    process_body = process_certificate[process_start:process_end if process_end >= 0 else None]
    for dependency in (
            'source_expands_with_scopes certificate',
            'checkFresh_sound_with_intervals',
            'certifiedBinderTokenChunks_pairwise_disjoint',
            'certifiedBinderTokenChunks_freshness',
            'binderTokenSequence_avoids_source_class'):
        if dependency not in process_body:
            raise ValueError(f'process-level binder freshness omits: {dependency}')
    macro_termination = (root / 'NLisp/MacroTermination.lean').read_text(encoding='utf-8')
    full_copy_start = macro_termination.find(
        'theorem literal_call_at_list_index_full_copy_certified_rank_decreases')
    full_copy_end = macro_termination.find('\n/--', full_copy_start + 1)
    full_copy_proof = macro_termination[
        full_copy_start:full_copy_end if full_copy_end >= 0 else None]
    if full_copy_start < 0 or any(dependency not in full_copy_proof for dependency in (
            'copyManyWithMacros_extract_element', 'selectedChildAccepted',
            'ExpansionCertificate.checkStep_sound', 'template_static_call_rank_decreases')):
        raise ValueError('full parent-copy to certified sibling rank theorem is incomplete')
    if 'import NLisp.MacroTermination' not in aggregate:
        raise ValueError('macro termination connection is not in NLisp.lean')
    lambda_counter = macro_termination.find(
        'theorem copyWithMacros_lambda_atomic_body_final_counter')
    lambda_counter_end = macro_termination.find('\n/--', lambda_counter + 1)
    lambda_counter_proof = macro_termination[
        lambda_counter:lambda_counter_end if lambda_counter_end >= 0 else None]
    if lambda_counter < 0 or any(dependency not in lambda_counter_proof for dependency in (
            'copyWithMacros_lambda_parts', 'copyParameters_counter_with_macros',
            'copyWithMacros_atom_keeps_counter')):
        raise ValueError('lambda dispatcher final-counter theorem is incomplete')
    let_counter = macro_termination.find(
        'theorem copyWithMacros_let_counter_preserving_body_final_counter')
    let_counter_end = macro_termination.find('\n/--', let_counter + 1)
    let_counter_proof = macro_termination[
        let_counter:let_counter_end if let_counter_end >= 0 else None]
    if let_counter < 0 or any(dependency not in let_counter_proof for dependency in (
            'copyWithMacros_let_parts', 'copyBindingsWithMacros_preserving_counter',
            'macroCounterSafeBindingInputs_preserving', 'bodyPreserving')):
        raise ValueError('let dispatcher final-counter theorem is incomplete')
    let_fresh = macro_termination.find(
        'theorem copyWithMacros_let_binding_tokens_fresh')
    let_fresh_end = macro_termination.find('\n/--', let_fresh + 1)
    let_fresh_proof = macro_termination[
        let_fresh:let_fresh_end if let_fresh_end >= 0 else None]
    if let_fresh < 0 or any(dependency not in let_fresh_proof for dependency in (
            'MacroCounterSafeBindingInputs', 'macroCounterSafeBindingInputs_preserving',
            'copyBindingsWithMacros_preserving_tokens_unique',
            'copyBindingsWithMacros_preserving_tokens_avoid_source',
            'copyBindingsWithMacros_preserving_tokens_within_interval')):
        raise ValueError('let dispatcher binder freshness theorem is incomplete')
    for theorem, dependencies, label in (
            ('copyWithMacros_let_hole_binding_tokens_fresh',
             ('MacroCounterSafeBindingInputs', 'macroCounterSafeBindingInputs_preserving',
              'copyBindingsWithMacros_preserving_tokens_unique'), 'hole-let'),
            ('copyWithMacros_match_case_tokens_fresh',
             ('MacroCounterSafeCases', 'macroCounterSafeCases_preserving',
              'copyCasesWithMacros_preserving_tokens_unique'), 'match-case'),
            ('copyWithMacros_match_hole_case_tokens_fresh',
             ('MacroCounterSafeCases', 'macroCounterSafeCases_preserving',
              'copyCasesWithMacros_preserving_tokens_unique'), 'hole-match-case')):
        start = macro_termination.find(f'theorem {theorem}')
        end = macro_termination.find('\n/--', start + 1)
        proof = macro_termination[start:end if end >= 0 else None]
        if start < 0 or any(dependency not in proof for dependency in dependencies):
            raise ValueError(f'{label} dispatcher binder freshness theorem is incomplete')
    source_reader = (root / 'NLisp/SourceReader.lean').read_text(encoding='utf-8')
    c_expansion = (root / 'NLisp/CExpansion.lean').read_text(encoding='utf-8')
    legacy_source_ids = len(re.findall(
        r'3\s*\*\s*\(index\s*\+\s*1\)\s*\+\s*1', source_reader)) >= 3
    lexer_start = source_reader.find('def lexLoop ')
    lexer_end = source_reader.find('\ndef lex ', lexer_start + 1)
    lexer_source = source_reader[lexer_start:lexer_end] if lexer_start >= 0 and lexer_end >= 0 else ''
    factored_source_ids = (
        re.search(r'def\s+sourceAtom\s*\(text : String\)\s*\(index : Nat\)\s*:\s*Token\s*:=\s*'
                  r'\.atom text \(3 \* \(index \+ 1\) \+ 1\)', source_reader) is not None and
        len(re.findall(r'\bsourceAtom\b', lexer_source)) == 4 and
        re.search(r'identity : Nat\)\s*→\s*identity % 3 = 1 → Token', source_reader) is not None and
        'theorem sourceAtom_identity_class ' in source_reader)
    if not legacy_source_ids and not factored_source_ids:
        raise ValueError('SourceReader no longer assigns source-class IDs to every atom form')
    if 'some (.atom ⟨name, none, identity⟩, tail)' not in source_reader:
        raise ValueError('SourceReader parsing no longer preserves lexer atom identities')
    if not re.search(
            r'atom\.origin\.isNone\s*&&\s*atom\.token\s*%\s*3\s*==\s*1',
            c_expansion):
        raise ValueError('CExpansion source atom validity no longer uses reserved source class')


def verify_checker_full_cost_contract():
    """Pin the environment-scan component of the checker cost model."""
    root = pathlib.Path(__file__).resolve().parents[1]
    source = (root / 'NLisp/CertificateSize.lean').read_text(encoding='utf-8')
    binding_walk = (root / 'NLisp/CBindingWalk.lean').read_text(encoding='utf-8')
    required = (
        'def siteFullCostBitsBound ',
        'theorem acceptsLookupBudget_le_siteLookupBitsBound',
        'theorem acceptsWithFullCost_le_siteFullCostBitsBound',
        'theorem checkSitesWithFullCost_le_siteFullCostBitsBounds',
        'def checkWithFullCostBitsBound ',
        'theorem checkWithFullCost_le_checkWithFullCostBitsBound',
        'theorem checkWithFullCost_le_referencedSitesBits_squared',
    )
    for declaration in required:
        if declaration not in source:
            raise ValueError(f'checker full-cost environment bound missing: {declaration}')
    for declaration in (
            'theorem walk_atom_sites_length_le_one',
            'theorem walk_atom_sites_le_nodeCount',
            'theorem walk_nilNone_sites_le_nodeCount',
            'theorem walkMany_sites_le_nodeCount',
            'theorem walkMany_atomList_sites_le_nodeCount',
            'theorem nodeListNodeCount_atomList_eq_length',
            'theorem walkMany_atomList_sites_le_length',
            'theorem walk_ordinaryAtomList_sites_le_length',
            'theorem nodeCount_atomList',
            'theorem walk_ordinaryAtomList_sites_le_nodeCount',
            'theorem nodeCount_list_eq_annotatedNodeListCount',
            'theorem annotatedNodeListCount_atomList_eq_length',
            'theorem walkMany_atomList_sites_le_annotatedNodeCount',
            'def annotatedNodeListCount',
            'theorem walkMany_sites_le_annotatedNodeCount',
            'theorem walkMany_sites_le_annotatedNodeCount_of_rows'):
        if declaration not in binding_walk:
            raise ValueError(
                f'binding-walk input-size groundwork omits: {declaration}')
    atom_node_start = binding_walk.find('theorem walk_atom_sites_le_nodeCount')
    atom_node_end = binding_walk.find('\ntheorem walkMany_atomList_sites_le_nodeCount',
                                     atom_node_start)
    atom_node_proof = binding_walk[atom_node_start:atom_node_end]
    if 'walk_atom_sites_length_le_one' not in atom_node_proof or \
            'Node.nodeCount' not in atom_node_proof:
        raise ValueError(
            'atomic walk bound is not derived from the atom reference bound and node measure')
    nil_none_start = binding_walk.find('theorem walk_nilNone_sites_le_nodeCount')
    nil_none_end = binding_walk.find('\ntheorem walkMany_atomList_sites_le_nodeCount',
                                   nil_none_start)
    nil_none_proof = binding_walk[nil_none_start:nil_none_end]
    if 'nilOrNone' not in nil_none_proof or 'sitesEmpty' not in nil_none_proof or \
            'Node.nodeCount' not in nil_none_proof:
        raise ValueError(
            'Nil/None walker case is not connected to its empty-site node bound')
    atom_list_start = binding_walk.find(
        'theorem walkMany_atomList_sites_le_nodeCount')
    atom_list_end = binding_walk.find('\ndef walkDeclaration', atom_list_start)
    atom_list_proof = binding_walk[atom_list_start:atom_list_end]
    for dependency in ('walk_atom_sites_length_le_one', 'ih fuel tailSites',
                       'nodeListNodeCount', 'List.length_append',
                       'atomNodeCount'):
        if dependency not in atom_list_proof:
            raise ValueError(
                'flat atom-list reference-site bound no longer composes '
                f'its structural premises: {dependency}')
    length_bound_start = binding_walk.find(
        'theorem walkMany_atomList_sites_le_length')
    length_bound_end = binding_walk.find('\ndef walkDeclaration', length_bound_start)
    length_bound = binding_walk[length_bound_start:length_bound_end]
    if 'walkMany_atomList_sites_le_nodeCount' not in length_bound or \
            'nodeListNodeCount_atomList_eq_length' not in length_bound:
        raise ValueError(
            'flat atom-list site-count theorem is not reduced to input length')
    ordinary_start = binding_walk.find(
        'theorem walk_ordinaryAtomList_sites_le_length')
    ordinary_end = binding_walk.find('\ndef walkDeclaration', ordinary_start)
    ordinary_proof = binding_walk[ordinary_start:ordinary_end]
    if 'walkOrdinaryHead' not in ordinary_proof or \
            'walkMany_atomList_sites_le_length' not in ordinary_proof:
        raise ValueError(
            'ordinary application walk does not reduce to the flat-list bound')
    node_count_start = binding_walk.find(
        'theorem walk_ordinaryAtomList_sites_le_nodeCount')
    node_count_end = binding_walk.find('\ndef walkDeclaration', node_count_start)
    node_count_proof = binding_walk[node_count_start:node_count_end]
    if 'nodeCount_list_eq_annotatedNodeListCount' not in node_count_proof or \
            'walkMany_atomList_sites_le_annotatedNodeCount' not in node_count_proof:
        raise ValueError(
            'ordinary application bound is not expressed in annotated tree nodes')
    annotated_atoms_start = binding_walk.find(
        'theorem walkMany_atomList_sites_le_annotatedNodeCount')
    annotated_atoms_end = binding_walk.find('\ndef walkDeclaration', annotated_atoms_start)
    annotated_atoms_proof = binding_walk[annotated_atoms_start:annotated_atoms_end]
    if 'walkMany_sites_le_annotatedNodeCount_of_rows' not in annotated_atoms_proof or \
            'walk_atom_sites_le_nodeCount' not in annotated_atoms_proof or \
            'List.mem_map.mp' not in annotated_atoms_proof:
        raise ValueError(
            'atom-list bound does not use row-indexed pointwise walk evidence')
    annotated_walk_start = binding_walk.find(
        'theorem walkMany_sites_le_annotatedNodeCount')
    annotated_walk_end = binding_walk.find(
        '\ntheorem walk_atom_sites_length_le_one', annotated_walk_start)
    annotated_walk_proof = binding_walk[
        annotated_walk_start:annotated_walk_end]
    if 'annotatedNodeListCount_cons' not in annotated_walk_proof or \
            'walkBound' not in annotated_walk_proof:
        raise ValueError(
            'annotated syntax list-walk bound omits its pointwise node-cost premise')
    row_walk_start = binding_walk.find(
        'theorem walkMany_sites_le_annotatedNodeCount_of_rows')
    row_walk_end = binding_walk.find('\ntheorem walk_atom_sites_length_le_one', row_walk_start)
    row_walk_proof = binding_walk[row_walk_start:row_walk_end]
    if 'tree ∈ trees' not in row_walk_proof or \
            'List.mem_cons_of_mem' not in row_walk_proof:
        raise ValueError(
            'row-indexed annotated walk bound does not preserve membership through recursion')
    site_theorem = source.find('theorem acceptsWithFullCost_le_siteFullCostBitsBound')
    site_end = source.find('\n/--', site_theorem + 1)
    site_proof = source[site_theorem:site_end if site_end >= 0 else None]
    for dependency in (
            'acceptsWithFullCost_cost_le',
            'acceptsLookupBudget_le_siteLookupBitsBound',
            'cBindingEnvironmentLength_le_bits',
            'environmentSquareBound', 'callerSquareBound'):
        if dependency not in site_proof:
            raise ValueError(f'checker site cost proof omits: {dependency}')
    whole_theorem = source.find('theorem checkWithFullCost_le_checkWithFullCostBitsBound')
    whole_end = source.find('\n/--', whole_theorem + 1)
    whole_proof = source[whole_theorem:whole_end if whole_end >= 0 else None]
    if 'checkSitesWithFullCost_le_siteFullCostBitsBounds' not in whole_proof:
        raise ValueError('checker whole-site cost theorem omits local cost composition')


def verify_c_utf8_reader():
    """Check that C's UTF-8 and literal readers retain the modeled contract.

    The Lean codec proofs establish the scalar-level round trip. This check
    pins the corresponding C branches and the explicit-length Text result so
    source drift cannot silently invalidate that comparison. It is a
    structural source check, not a proof of C execution semantics.
    """
    root = pathlib.Path(__file__).resolve().parents[1]
    source = (root / 'src/nlisp.c').read_text(encoding='utf-8')
    lexical = (root / 'NLisp/Lexical.lean').read_text(encoding='utf-8')

    def body(start_marker, end_marker, description):
        start = source.find(start_marker)
        end = source.find(end_marker, start + 1)
        if start < 0 or end < 0:
            raise ValueError(f'C {description} implementation was not found')
        return source[start:end]

    def require(text, pattern, description):
        if re.search(pattern, text, flags=re.S) is None:
            raise ValueError(f'C UTF-8 reader contract missing: {description}')

    scalar = body('static bool scalar(uint32_t c) {',
                  'static bool utf8_next(', 'Unicode scalar predicate')
    require(scalar, r'c\s*<=\s*0x10ffffU', 'maximum Unicode scalar is U+10FFFF')
    require(scalar, r'c\s*>=\s*0xd800U\s*&&\s*c\s*<=\s*0xdfffU',
            'surrogate codepoints are excluded')

    decoder = body('static bool utf8_next(', 'static void utf8_put(', 'utf8_next')
    for pattern, description in (
        (r'first\s*<\s*0x80U', 'ASCII bytes decode directly'),
        (r'first\s*>=\s*0xc2U\s*&&\s*first\s*<=\s*0xdfU',
         'two-byte leads reject overlong C0/C1'),
        (r'first\s*>=\s*0xe0U\s*&&\s*first\s*<=\s*0xefU',
         'three-byte lead range'),
        (r'first\s*>=\s*0xf0U\s*&&\s*first\s*<=\s*0xf4U',
         'four-byte leads stop at F4'),
        (r'\(next\s*&\s*0xc0U\)\s*!=\s*0x80U',
         'every continuation byte is checked'),
        (r'value\s*<\s*minimum\s*\|\|\s*!scalar\(value\)',
         'overlong and nonscalar sequences are rejected')):
        require(decoder, pattern, description)

    for pattern, description in (
        (r'value\s*=\s*first\s*&\s*31U', 'two-byte lead payload mask'),
        (r'value\s*=\s*first\s*&\s*15U', 'three-byte lead payload mask'),
        (r'value\s*=\s*first\s*&\s*7U', 'four-byte lead payload mask'),
        (r'value\s*=\s*\(value\s*<<\s*6\)\s*\|\s*\(next\s*&\s*63U\)',
         'continuation accumulation')
    ):
        require(decoder, pattern, description)

    for name, expression, description in (
        ('utf8Pair', r'\(first\.toNat\s*%\s*32\)\s*\*\s*64\s*\+\s*'
         r'\(second\.toNat\s*%\s*64\)', 'two-byte payload reconstruction'),
        ('utf8Triple', r'\(first\.toNat\s*%\s*16\)\s*\*\s*4096\s*\+\s*'
         r'\(second\.toNat\s*%\s*64\)\s*\*\s*64\s*\+\s*third\.toNat\s*%\s*64',
         'three-byte payload reconstruction'),
        ('utf8Quad', r'\(first\.toNat\s*%\s*8\)\s*\*\s*262144\s*\+\s*'
         r'\(second\.toNat\s*%\s*64\)\s*\*\s*4096\s*\+\s*'
         r'\(third\.toNat\s*%\s*64\)\s*\*\s*64\s*\+\s*fourth\.toNat\s*%\s*64',
         'four-byte payload reconstruction')):
        if re.search(rf'private def {name}.*?:\s*Nat\s*:=\s*{expression}',
                     lexical, flags=re.S) is None:
            raise ValueError(f'Lean UTF-8 decoder contract missing: {description}')

    lean_decoder = lexical[lexical.find('def utf8Next'):lexical.find(
        '/-- The two-byte decoder branch')]
    for pattern, description in (
        (r'first\.toNat\s*<\s*0x80', 'Lean ASCII lead range'),
        (r'0xc2\s*≤\s*first\.toNat\s*&&\s*first\.toNat\s*≤\s*0xdf',
         'Lean two-byte lead range'),
        (r'0xe0\s*≤\s*first\.toNat\s*&&\s*first\.toNat\s*≤\s*0xef',
         'Lean three-byte lead range'),
        (r'0xf0\s*≤\s*first\.toNat\s*&&\s*first\.toNat\s*≤\s*0xf4',
         'Lean four-byte lead range'),
        (r'value\s*<\s*0x80\s*\|\|\s*!utf8Scalar\s+value',
         'Lean two-byte overlong/scalar rejection'),
        (r'value\s*<\s*0x800\s*\|\|\s*!utf8Scalar\s+value',
         'Lean three-byte overlong/scalar rejection'),
        (r'value\s*<\s*0x10000\s*\|\|\s*!utf8Scalar\s+value',
         'Lean four-byte overlong/scalar rejection')):
        require(lean_decoder, pattern, description)
    lean_scalar = lexical[lexical.find('private def utf8Scalar'):lexical.find(
        '/-- The scalar-to-byte operation')]
    require(lean_scalar, r'value\s*≤\s*0x10ffff', 'Lean scalar upper bound')
    require(lean_scalar, r'0xd800\s*≤\s*value\s*&&\s*value\s*≤\s*0xdfff',
            'Lean scalar surrogate exclusion')

    encoder = body('static void utf8_put(', 'static bool unicode_escape(', 'utf8_put')
    for pattern, description in (
        (r'c\s*<\s*0x80U.*?\(char\)c', 'one-byte encoding'),
        (r'c\s*<\s*0x800U.*?0xc0U\s*\|\s*\(c\s*>>\s*6\).*?'
         r'0x80U\s*\|\s*\(c\s*&\s*63U\)',
         'two-byte lead and continuation payloads'),
        (r'c\s*<\s*0x10000U.*?0xe0U\s*\|\s*\(c\s*>>\s*12\).*?'
         r'0x80U\s*\|\s*\(\(c\s*>>\s*6\)\s*&\s*63U\).*?'
         r'0x80U\s*\|\s*\(c\s*&\s*63U\)',
         'three-byte lead and continuation payloads'),
        (r'0xf0U\s*\|\s*\(c\s*>>\s*18\).*?'
         r'0x80U\s*\|\s*\(\(c\s*>>\s*12\)\s*&\s*63U\).*?'
         r'0x80U\s*\|\s*\(\(c\s*>>\s*6\)\s*&\s*63U\).*?'
         r'0x80U\s*\|\s*\(c\s*&\s*63U\)',
         'four-byte lead and all continuation payloads')):
        require(encoder, pattern, description)

    lean_encoder = lexical[lexical.find('def utf8PutCodepoint'):lexical.find(
        '/-- Encode a sequence of Unicode scalar values')]
    for pattern, description in (
        (r'value\s*/\s*64.*?value\s*%\s*64',
         'two-byte quotient/remainder payloads'),
        (r'value\s*/\s*4096.*?\(value\s*/\s*64\)\s*%\s*64.*?value\s*%\s*64',
         'three-byte quotient/remainder payloads'),
        (r'value\s*/\s*262144.*?\(value\s*/\s*4096\)\s*%\s*64.*?'
         r'\(value\s*/\s*64\)\s*%\s*64.*?value\s*%\s*64',
         'four-byte quotient/remainder payloads')):
        require(lean_encoder, pattern, description)

    unicode = body('static bool unicode_escape(', 'static bool string_literal(',
                   'unicode_escape')
    require(unicode, r'\+\+digits\s*>\s*6U', 'Unicode escapes have at most six digits')
    require(unicode, r'!scalar\(c\)', 'Unicode escapes reject nonscalar values')

    string_reader = body('static bool string_literal(', 'static bool character_literal(',
                         'string_literal')
    require(string_reader, r'utf8_next\(s,\s*length\s*-\s*1U,\s*&i,\s*&c\)',
            'quoted string payload is decoded as UTF-8 before its closing quote')
    require(string_reader, r'utf8_put\(decoded,\s*&used,\s*c\)',
            'decoded scalars are encoded into the returned Text buffer')
    require(string_reader, r'out->data\s*=\s*decoded;\s*out->length\s*=\s*used',
            'Text carries an explicit byte length, including embedded NUL')
    c_string_escapes = (
        (r"case 'n':\s*c\s*=\s*'\\n';\s*i\+\+;\s*break;", 'newline escape'),
        (r"case 'r':\s*c\s*=\s*'\\r';\s*i\+\+;\s*break;", 'carriage-return escape'),
        (r"case 't':\s*c\s*=\s*'\\t';\s*i\+\+;\s*break;", 'tab escape'),
        (r"case '\"':\s*c\s*=\s*'\"';\s*i\+\+;\s*break;", 'quoted-quote escape'),
        (r"case '\\\\':\s*c\s*=\s*'\\\\';\s*i\+\+;\s*break;", 'backslash escape'),
        (r"case 'u':\s*if\s*\(!unicode_escape\(s,\s*&i,\s*&c\)\)\s*return false;\s*break;",
         'braced Unicode scalar escape'),
        (r'default:\s*return false;', 'unknown escapes are rejected'))
    for pattern, description in c_string_escapes:
        require(string_reader, pattern, description)
    if re.search(r'else\s+if\s*\(!utf8_next\(s,\s*length\s*-\s*1U,\s*&i,\s*&c\)\s*\|\|\s*c\s*==\s*\x27\x22\x27',
                 string_reader, flags=re.S) is None:
        raise ValueError('C string reader no longer rejects unescaped quote payloads')

    lean_escape_start = lexical.find('private def decodeStringBody')
    lean_escape_end = lexical.find('/-- Decode the quoted atom spelling', lean_escape_start + 1)
    if lean_escape_start < 0 or lean_escape_end < 0:
        raise ValueError('Lean string escape decoder was not found')
    lean_string_escapes = lexical[lean_escape_start:lean_escape_end]
    for fragment, description in (
            ("'\\\\' :: 'n' :: tail", 'Lean newline escape'),
            ("'\\\\' :: 'r' :: tail", 'Lean carriage-return escape'),
            ("'\\\\' :: 't' :: tail", 'Lean tab escape'),
            ("'\\\\' :: '\"' :: tail", 'Lean quoted-quote escape'),
            ("'\\\\' :: '\\\\' :: tail", 'Lean backslash escape'),
            ('readUnicodeEscape rest', 'Lean braced Unicode scalar escape'),
            ("'\"' :: _ => none", 'Lean rejection of unescaped quote')):
        if fragment not in lean_string_escapes:
            raise ValueError(f'Lean string literal contract missing: {description}')
    if 'readStringLiteral_escape_table' not in lexical:
        raise ValueError('Lean string literal escape-table theorem is missing')

    character_reader = body('static bool character_literal(',
                            '/* Unicode 18.0 White_Space', 'character_literal')
    require(character_reader,
            r'length\s*<\s*3U\s*\|\|\s*s\[0\]\s*!=\s*\x27#\x27\s*\|\|\s*s\[1\]\s*!=\s*\x27\\\\\x27',
            'character spelling has the # backslash prefix and a nonempty body')
    for spelling, scalar, description in (
            ('newline', r"'\\n'", 'named newline character'),
            ('space', r"' '\s*", 'named space character'),
            ('tab', r"'\\t'", 'named tab character')):
        require(character_reader,
                rf'strcmp\(s\s*\+\s*2U,\s*"{spelling}"\)\s*==\s*0.*?\*out\s*=\s*{scalar}',
                description)
    require(character_reader, r'utf8_next\(s,\s*length,\s*&i,\s*out\)\s*&&\s*i\s*==\s*length',
            'character literals contain exactly one decoded scalar')
    require(character_reader, r'unicode_escape\(s,\s*&i,\s*out\)\s*&&\s*i\s*==\s*length',
            'Unicode character escapes consume the complete token')
    lean_character_start = lexical.find('def readCharacterLiteral ')
    lean_character_end = lexical.find('\nprivate def utf8Continuation', lean_character_start + 1)
    if lean_character_start < 0 or lean_character_end < 0:
        raise ValueError('Lean character literal reader was not found')
    lean_character = lexical[lean_character_start:lean_character_end]
    for contract in ("'#' :: '\\\\' :: body", "body == ['n','e','w','l','i','n','e']",
                     "body == ['s','p','a','c','e']", "body == ['t','a','b']",
                     "| [scalar] => pure scalar", 'readUnicodeEscape body'):
        if contract not in lean_character:
            raise ValueError(f'Lean character literal contract missing: {contract}')

    c_lexer = body('static bool lex(Arena *a, const char *src, size_t len, Tokens *out, Error *e) {',
                   'static bool parse_forms(', 'source lexer')
    require(c_lexer,
            r'while\s*\(p\s*<\s*len\)\s*if\s*\(!utf8_next\(src,\s*len,\s*&p,\s*&c\)\s*\|\|\s*c\s*==\s*0U\)\s*return\s+fail\(e,\s*NLISP_PARSE_ERROR',
            'invalid UTF-8 and embedded NUL are reported as parse faults')
    require(c_lexer, r'"invalid UTF-8 or NUL in source"',
            'reader fault identifies invalid UTF-8/NUL input')

    file_reader = body('static char *read_source(', 'static void report(', 'file reader')
    require(file_reader,
            r'fail\(e,\s*NLISP_IO_ERROR,.*?cannot open file',
            'open failures are IO errors')
    require(file_reader,
            r'fail\(e,\s*NLISP_IO_ERROR,.*?cannot determine file size',
            'file size failures are IO errors')
    require(file_reader,
            r'fail\(e,\s*NLISP_IO_ERROR,.*?cannot read file',
            'short reads and close failures are IO errors')
    process_file = body('static NLispStatus nlisp_process_file_inner(',
                        'NLispStatus nlisp_process_file(', 'top-level file reader pipeline')
    require(process_file,
            r'source\s*=\s*read_source\(path,\s*&len,\s*&e\).*?source\s*!=\s*NULL\s*&&\s*lex\(&a,\s*source,\s*len,\s*&ts,\s*&e\)\s*&&\s*parse_forms\(&a,\s*ts,\s*&forms,\s*&e\)',
            'file read proceeds through lexing and parsing in order')
    require(process_file, r'if\s*\(e\.set\).*?return\s+e\.status',
            'reader errors are returned as the stored status')

    apply = body('static Value *apply(Runtime *r, Value *f, Value **args, size_t n, Span span) {',
                 'static Value *eval(Runtime *r, const SExpr *x, RBind *env) {',
                 'builtin apply dispatcher')
    for pattern, description in (
        (r'BI_STRING_EQ\s*\|\|\s*f->as\.builtin\s*==\s*BI_STRING_APPEND\s*\|\|\s*f->as\.builtin\s*==\s*BI_CHAR_EQ',
         'string and character primitives enter the text builtin branch'),
        (r'args\[0\]->as\.text\.length\s*==\s*args\[1\]->as\.text\.length\s*&&\s*memcmp\(args\[0\]->as\.text\.data,\s*args\[1\]->as\.text\.data,\s*args\[0\]->as\.text\.length\)\s*==\s*0',
         'string equality compares byte length and contents'),
        (r'v->as\.text\.length\s*=\s*left\.length\s*\+\s*right\.length',
         'string append sums explicit byte lengths'),
        (r'left\.length\s*>\s*SIZE_MAX\s*-\s*right\.length\s*-\s*1U',
         'string append rejects overflow before allocating its terminator'),
        (r'memcpy\(v->as\.text\.data,\s*left\.data,\s*left\.length\)',
         'string append copies the left byte sequence'),
        (r'memcpy\(v->as\.text\.data\s*\+\s*left\.length,\s*right\.data,\s*right\.length\)',
         'string append copies the right byte sequence after the left'),
        (r'args\[0\]->as\.character\s*==\s*args\[1\]->as\.character',
         'character equality compares decoded scalar values')):
        require(apply, pattern, description)

    source_reader = (root / 'NLisp/SourceReader.lean').read_text(encoding='utf-8')
    public_header = (root / 'include/nlisp.h').read_text(encoding='utf-8')
    for theorem in ('read_failure_iff', 'readWithFuel_failure_iff',
                    'readBytesWithFuel_failure_iff',
                    'readBytesFailureKind_some_iff',
                    'readBytesFailureKind_invalidUtf8_iff',
                    'readBytesFailureKind_embeddedNul_iff',
                    'readBytesFailureKind_lexical_iff',
                    'readBytesFailureKind_parse_iff',
                    'readBytesFailureStatus_parseError_iff',
                    'SourceReadFailure.cStatus_parseError',
                    'CFileReadFailure.status_classification',
                    'CFileReadFailure.status_code'):
        if theorem not in source_reader:
            raise ValueError(f'Lean source reader fault partition missing: {theorem}')
    for kind in ('.invalidUtf8', '.embeddedNul', '.lexical', '.parse'):
        if kind not in source_reader:
            raise ValueError(f'Lean source reader fault class missing: {kind}')
    for pattern, description in (
        (r'NLISP_IO_ERROR\s*=\s*3', 'public I/O status value'),
        (r'NLISP_PARSE_ERROR\s*=\s*4', 'public parse status value')):
        require(public_header, pattern, description)

    for theorem in ('utf8PutCodepoint_ascii_eq_lean',
                    'utf8PutCodepoint_length',
                    'encodeUtf8Codepoints_ascii_chars',
                    'encodeUtf8String_ascii_chars',
                    'encodeUtf8String_eq_native_utf8_of_ascii',
                    'utf8Next_rejects_invalid_lead',
                    'utf8Next_rejects_bad_twoByte_continuation',
                    'utf8Next_rejects_bad_threeByte_second',
                    'utf8Next_rejects_bad_threeByte_third',
                    'utf8Next_rejects_bad_fourByte_second',
                    'utf8Next_rejects_bad_fourByte_third',
                    'utf8Next_rejects_bad_fourByte_fourth',
                    'utf8Next_utf8PutCodepoint_append',
                    'decodeUtf8Fuel_encodeUtf8Codepoints',
                    'decodeUtf8_encodeUtf8Codepoints',
                    'utf8Next_encodeUtf8String_singleton_append',
                    'decodeUtf8_encodeUtf8String_exact',
                    'encodeUtf8String_injective',
                    'encodeUtf8String_eq_iff',
                    'encodeUtf8String_append',
                    'decodeUtf8_encodeUtf8String_append',
                    'CTextModel.stringEqual_ofString_iff',
                    'CTextModel.stringAppend_ofString',
                    'CTextModel.stringAppend_byteLength',
                    'CTextModel.stringAppend_assoc',
                    'CTextModel.stringAppend_empty',
                    'readStringLiteral_preserves_embedded_nul',
                    'readStringLiteral_cText_preserves_embedded_nul',
                    'CTextModel.embeddedNul_append_is_lengthBearing',
                    'CTextModel.stringEqual_embeddedNul_not_prefix',
                    'cCharacterPayload_encodeUtf8String_singleton',
                    'readCharacterLiteral_named_matches_cCharacterPayload',
                    'readCharacterLiteral_single_scalar',
                    'readCharacterLiteral_unicode_escape_boundaries',
                    'readCharacterLiteral_rejects_surrogate_escape'):
        if theorem not in lexical:
            raise ValueError(f'Lean UTF-8/literal contract theorem missing: {theorem}')

    scalar_roundtrip_start = lexical.find('theorem decodeUtf8Fuel_encodeUtf8Codepoints')
    scalar_roundtrip_end = lexical.find('\n/--', scalar_roundtrip_start + 1)
    scalar_roundtrip = lexical[
        scalar_roundtrip_start:scalar_roundtrip_end if scalar_roundtrip_end >= 0 else None]
    for dependency in ('utf8Next_utf8PutCodepoint_append',
                       'validHead', 'validTail', 'tailBound', 'decodeUtf8Fuel'):
        if dependency not in scalar_roundtrip:
            raise ValueError(
                f'Lean scalar-list UTF-8 roundtrip omits proof dependency: {dependency}')
    scalar_roundtrip_wrapper_start = lexical.find('theorem decodeUtf8_encodeUtf8Codepoints')
    scalar_roundtrip_wrapper_end = lexical.find('\n/--', scalar_roundtrip_wrapper_start + 1)
    scalar_roundtrip_wrapper = lexical[
        scalar_roundtrip_wrapper_start:scalar_roundtrip_wrapper_end
        if scalar_roundtrip_wrapper_end >= 0 else None]
    if 'decodeUtf8Fuel_encodeUtf8Codepoints' not in scalar_roundtrip_wrapper:
        raise ValueError('unbounded UTF-8 scalar roundtrip omits its fuel-bound proof')


def verify_c_binary64_contract():
    """Pin the C decimal-to-binary64 algorithm and Lean reader model.

    This checks the source-level premises and major branches of the exact C
    converter against the Lean parser's corresponding model. It is a drift
    detector; it does not establish bit-for-bit semantic equivalence.
    """
    root = pathlib.Path(__file__).resolve().parents[1]
    source = (root / 'src/nlisp.c').read_text(encoding='utf-8')
    lexical = (root / 'NLisp/Lexical.lean').read_text(encoding='utf-8')

    def require(text, pattern, description):
        if re.search(pattern, text, flags=re.S) is None:
            raise ValueError(f'binary64 conversion contract missing: {description}')

    require(source, r'_Static_assert\([^;]*DBL_MANT_DIG\s*==\s*53\s*&&\s*DBL_MAX_EXP\s*==\s*1024',
            'C double is IEEE binary64')
    rounder_start = source.find('static uint64_t round_ratio_scaled(')
    converter_start = source.find('static double decimal_to_binary64(', rounder_start + 1)
    parser_start = source.find('static bool float_atom(', converter_start + 1)
    next_function = source.find('static bool require(', parser_start + 1)
    if min(rounder_start, converter_start, parser_start, next_function) < 0:
        raise ValueError('C binary64 conversion functions were not found')
    rounder = source[rounder_start:converter_start]
    converter = source[converter_start:parser_start]
    parser = source[parser_start:next_function]
    for pattern, description in (
        (r'mpz_mul_2exp\(twice_remainder,\s*remainder,\s*1U\)',
         'exact remainder comparison'),
        (r'mpz_cmp\(twice_remainder,\s*scaled_denominator\)\s*==\s*0\s*&&\s*mpz_odd_p\(quotient\)',
         'ties round to even')):
        require(rounder, pattern, description)
    for pattern, description in (
        (r'round_ratio_scaled\(numerator,\s*denominator,\s*-1074\)',
         'subnormal rounding uses the binary64 minimum quantum'),
        (r'binary_exponent\s*>\s*1023', 'overflow becomes infinity'),
        (r'rounded\s*==\s*\(UINT64_C\(1\)\s*<<\s*53U\)',
         'normal rounding handles significand carry'),
        (r'bits\s*\|=\s*UINT64_C\(0x8000000000000000\)',
         'negative sign bit is preserved')):
        require(converter, pattern, description)
    for pattern, description in (
        (r"if\s*\(\*p\s*==\s*'-'\)\s*p\+\+", 'only an optional leading minus is accepted'),
        (r'if\s*\(!ascii_digit\(\*p\)\)\s*return\s+false',
         'integer part begins with an ASCII digit'),
        (r"if\s*\(\*p\+\+\s*!=\s*'\.'\s*\|\|\s*!ascii_digit\(\*p\)\)\s*return\s+false",
         'decimal point and at least one fractional digit are required'),
        (r'if\s*\(\*p\s*!=\s*\'\\0\'\)\s*return\s+false',
         'float token must be consumed completely'),
        (r'if\s*\(\*p\s*==\s*\'e\'\s*\|\|\s*\*p\s*==\s*\'E\'\)',
         'decimal exponent syntax')):
        require(parser, pattern, description)

    require(lexical, r'def\s+readFloatLiteral.*?if\s+floatLiteral\s+text\.toList.*?parseFloatLiteral',
            'Lean reader applies the decimal grammar before conversion')
    require(lexical, r'Float\.ofScientific\s+significand\s+\(scale\s*<\s*0\)\s+scale\.natAbs',
            'Lean conversion is based on exact integer significand and decimal scale')
    require(lexical, r'def\s+parseUnsignedFloatMagnitude.*?def\s+parseFloatLiteral.*?\|\s*\'-\'\s*::\s*rest\s*=>.*?\.map\s+Float\.neg',
            'source sign is applied once after unsigned magnitude conversion')
    for theorem in ('parseFloatLiteral_negative_sign_after_rounding',
                    'readFloatLiteral_positive_overflow_is_infinite',
                    'readFloatLiteral_negative_overflow_is_infinite',
                    'readFloatLiteral_positive_underflow_converts_to_zero',
                    'readFloatLiteral_negative_underflow_converts_to_zero'):
        if f'theorem {theorem}' not in lexical:
            raise ValueError(f'Lean binary64 sign/overflow contract missing: {theorem}')
    require(lexical, r'def\s+floatLiteral.*?exponentLiteral',
            'Lean syntax models optional signed exponent and decimal point')
    require(lexical, r'theorem\s+cFloatAtomSyntax_eq_floatLiteral',
            'C cursor grammar is proved equal to Lean float-token grammar')
    require(lexical, r'theorem\s+readFloatLiteral_satisfies_cFloatAtomSyntax',
            'every successfully read Lean float token satisfies C float syntax')

def verify_c_value_slot_runtime():
    """Pin the C shared-cell layout used by the Lean GlobalIR slot model.

    This is a source-structure check: it does not execute C pointer semantics.
    It makes drift in the mixed declaration index, cell allocation, closure
    capture, or initializer write visible to the independent verifier.
    """
    root = pathlib.Path(__file__).resolve().parents[1]
    source = (root / 'src/nlisp.c').read_text(encoding='utf-8')
    program_decl = re.search(
        r'typedef\s+struct\s*\{\s*Decl\s*\*data;\s*size_t\s+count;\s*\}\s*Program\s*;',
        source)
    if program_decl is None:
        raise ValueError('C Program.data mixed declaration layout was not found')

    start = source.find('static Value *run_program(Arena *a, Program *p, Error *e) {')
    end = source.find('static void print_value(', start + 1)
    if start < 0 or end < 0:
        raise ValueError('C run_program implementation was not found')
    body = source[start:end]

    def require(pattern, description):
        if re.search(pattern, body, flags=re.S) is None:
            raise ValueError(f'C run_program value-slot contract missing: {description}')

    require(r'RBind\s*\*\*value_slots\s*=\s*\(RBind\s*\*\*\)aalloc\(a,\s*p->count\s*\*\s*sizeof\(\*value_slots\)\)',
            'value_slots has one mixed-index entry per Program.data declaration')
    require(r'for\s*\(i\s*=\s*0U;\s*i\s*<\s*p->count;\s*i\+\+\)\s*if\s*\(p->data\[i\]\.kind\s*==\s*D_VAL\)\s*\{\s*env\s*=\s*rbind\(\s*&r,\s*env,\s*p->data\[i\]\.as\.val\.name,\s*NULL\s*\)\s*;\s*value_slots\[i\]\s*=\s*env\s*;\s*\}',
            'value_slots[i] points to the RBind cell allocated for that value declaration')
    require(r'for\s*\(i\s*=\s*0U;\s*i\s*<\s*count;\s*i\+\+\)\s*closures\[i\]->as\.closure\.env\s*=\s*env\s*;',
            'closures capture the shared global RBind environment')
    require(r'v\s*=\s*eval\(&r,\s*p->data\[i\]\.as\.val\.init,\s*env\)\s*;\s*if\s*\(v\s*==\s*NULL\)\s*return\s+NULL\s*;\s*value_slots\[i\]->value\s*=\s*v\s*;',
            'initializer evaluation writes through the saved RBind cell pointer')

    rbind = re.search(r'struct\s+RBind\s*\{\s*const\s+char\s*\*name;\s*Value\s*\*value;\s*RBind\s*\*next;\s*\}', source)
    if rbind is None:
        raise ValueError('C RBind shared value cell structure was not found')

    rbind_start = source.find('static RBind *rbind(Runtime *r, RBind *env, const char *name, Value *v) {')
    rbind_end = source.find('\nstatic RBind *rfind(', rbind_start + 1)
    if rbind_start < 0 or rbind_end < 0:
        raise ValueError('C rbind/rfind implementations were not found')
    rbind_body = source[rbind_start:rbind_end]
    if re.search(r'b->name\s*=\s*name;\s*b->value\s*=\s*v;\s*b->next\s*=\s*env;\s*return\s+b;',
                 rbind_body, flags=re.S) is None:
        raise ValueError('C rbind no longer prepends a shared cell to the environment')
    rfind_start = rbind_end + 1
    rfind_end = source.find('\nstatic Value *rlookup(', rfind_start)
    if rfind_end < 0:
        raise ValueError('C rfind implementation boundary was not found')
    rfind_body = source[rfind_start:rfind_end]
    if re.search(r'for\s*\(\s*;\s*env\s*!=\s*NULL\s*;\s*env\s*=\s*env->next\s*\)\s*'
                 r'if\s*\(\s*strcmp\(env->name,\s*name\)\s*==\s*0\s*\)\s*return\s+env;',
                 rfind_body, flags=re.S) is None:
        raise ValueError('C rfind no longer searches newest-to-oldest using string identity')

    lean_source = (root / 'NLisp/GlobalProgramEntry.lean').read_text(encoding='utf-8')
    name_resolution = (root / 'NLisp/CNameResolution.lean').read_text(encoding='utf-8')
    global_ir = (root / 'NLisp/GlobalIR.lean').read_text(encoding='utf-8')
    if ('theorem typed_getter_call_type_safe_or_early_read_in_environment' not in global_ir or
            'getter_call_reads_current_environment' not in global_ir):
        raise ValueError('GlobalIR typed getter safety in a closure environment is missing')
    for theorem in ('sourceValueSlotOrdinal_matches_identity_lookup',
                    'globalIndexOf_get?_unique',
                    'findNameIndex_matches_globalIndexOf',
                    'named_value_lookup_cell_and_getter_before_initialization',
                    'named_value_lookup_matches_initialized_getter',
                    'cValueSlotCellRead_matches_initialized_getter',
                    'mixed_value_identity_cell_and_getter_before_initialization',
                    'cIdentityLookup_value_reads_initialized_getter',
                    'cIdentityLookup_value_before_initialization',
                    'cIdentityLookup_value_faults_from_initial_store',
                    'cIdentityLookup_value_faults_after_prefix'):
        if f'theorem {theorem}' not in lean_source:
            raise ValueError(f'Lean mixed value-slot correspondence is missing: {theorem}')
    identity_lookup = re.search(
        r'def\s+globalIndexOf\s*\(target\s*:\s*Nat\)\s*:\s*List Entry\s*→\s*Option Nat\s*'
        r'\|\s*\[\]\s*=>\s*none\s*'
        r'\|\s*entry\s*::\s*rest\s*=>\s*if\s+identity entry == target\s+then\s+some 0\s*'
        r'else\s*\(globalIndexOf target rest\)\.map Nat\.succ', lean_source)
    if identity_lookup is None:
        raise ValueError('Lean global identity lookup no longer selects the first matching source declaration')
    for theorem in ('findName_prepend_shadows', 'findName_prepend_different',
                    'findNameIndex_sound', 'findNameIndex_complete'):
        if f'theorem {theorem}' not in name_resolution:
            raise ValueError(f'Lean linked-environment lookup contract is missing: {theorem}')


def verify_mixed_top_level_declaration_order():
    """Keep the original interleaved source position on function headers.

    GlobalHeader already retains its mixed source order. This check prevents
    function headers from silently losing that position when read together
    with top-level values.
    """
    root = pathlib.Path(__file__).resolve().parents[1]
    source = (root / 'NLisp/ExpansionLowering.lean').read_text(encoding='utf-8')
    if re.search(r'structure\s+Header\s+where[\s\S]*?order\s*:\s*Nat[\s\S]*?name\s*:\s*String', source) is None:
        raise ValueError('function Header no longer carries its mixed source order and name')
    if re.search(r'structure\s+GlobalHeader\s+where[\s\S]*?order\s*:\s*Nat[\s\S]*?name\s*:\s*String', source) is None:
        raise ValueError('value Header no longer carries its mixed source order and name')
    if re.search(r'readProgramHeaders[\s\S]*?some function\s*=>\s*'
                 r'let ordered := \{\s*function\s+with\s+order\s*:=\s*order\s*\}\s*'
                 r'pure\s*⟨ordered :: rest\.functions, rest\.globals,\s*'
                 r'TopLevelDeclaration\.function ordered :: rest\.declarations⟩', source) is None:
        raise ValueError('mixed top-level reader no longer stamps and retains function source order')
    for theorem in ('readProgramHeaders_cons_function', 'readProgramHeaders_cons_global',
                    'readProgramHeaders_declarations_project'):
        if f'theorem {theorem}' not in source:
            raise ValueError(f'mixed top-level source-order rule is missing: {theorem}')
    if 'ProgramHeaders.findNameIndex_selects_declaration' not in source:
        raise ValueError('named top-level lookup is not tied to a source declaration')
    decoder = (root / 'NLisp/NamedDecoder.lean').read_text(encoding='utf-8')
    if 'GlobalHeader.decodeHeader_order' not in decoder:
        raise ValueError('top-level value order is not preserved when building decoder headers')
    for theorem in ('decodeTopLevelProgramWithHeaders', 'decodeTopLevelProgramWithHeaders_project'):
        if theorem not in decoder:
            raise ValueError(f'decoded mixed source layout is not exposed/projection-checked: {theorem}')
    if 'GlobalHeader.decodeHeader' not in decoder or 'header.name' not in decoder:
        raise ValueError('top-level value declaration name is not retained by decoder headers')
    entry_source = (root / 'NLisp/GlobalProgramEntry.lean').read_text(encoding='utf-8')
    for theorem in ('namedGlobalLayout_of_identity_map', 'programHeaders_namedGlobalLayout',
                    'decodedTopLevelProgram_namedGlobalLayout',
                    'decodedTopLevelProgram_resolves_name_to_globalIndex'):
        if f'theorem {theorem}' not in entry_source:
            raise ValueError(f'decoded mixed declaration identity layout is missing: {theorem}')


def verify_global_ir_closure_application_safety():
    """Keep the generic GlobalIR closure-call preservation rule connected.

    The control-flow lemma is independent of the syntax fragment used to
    establish the closure body's result type; the contextual closure theorem
    must consume it rather than duplicate a weaker call-step argument.
    """
    root = pathlib.Path(__file__).resolve().parents[1]
    source = (root / 'NLisp/GlobalIR.lean').read_text(encoding='utf-8')
    helper_name = 'evaluate_closure_application_preserves_type_from_body_result'
    helper_start = source.find(f'theorem {helper_name}')
    if helper_start < 0:
        raise ValueError('generic GlobalIR closure application preservation rule is missing')
    helper_end = source.find('\n/- Any successful parallel evaluation', helper_start)
    helper = source[helper_start:helper_end if helper_end >= 0 else None]
    for contract in ('functionSuccess', 'argumentsSuccess', 'arityAgreement',
                     'bodySuccess', 'bodyResultTyped', 'callEq.trans bodySuccess'):
        if contract not in helper:
            raise ValueError(f'GlobalIR closure application rule omits {contract}')
    for theorem in ('evaluate_contextual_lambda_application_preserves_type',
                    'evaluate_contextual_closure_application_preserves_type'):
        contextual_start = source.find(f'theorem {theorem}')
        contextual_end = source.find('\n/- Any successful parallel evaluation', contextual_start)
        contextual = source[contextual_start:contextual_end if contextual_end >= 0 else None]
        if helper_name not in contextual:
            raise ValueError(f'{theorem} does not use the generic closure-call rule')
    runtime_theorem = 'evaluate_contextualGlobalRuntimeTerm_preserves_type'
    runtime_start = source.find(f'theorem {runtime_theorem}')
    if runtime_start < 0 or 'inductive ContextualGlobalRuntimeTerm' not in source:
        raise ValueError('contextual GlobalIR runtime/getter preservation fragment is missing')
    runtime_end = source.find('\ntheorem read_initialized', runtime_start)
    runtime = source[runtime_start:runtime_end if runtime_end >= 0 else None]
    for contract in ('evaluate_contextualGlobalArithmeticTerm_preserves_type',
                     'typed_getter_call_type_safe_or_early_read_in_environment',
                     'StoreWellTyped', 'earlyRead'):
        if contract not in runtime:
            raise ValueError(f'{runtime_theorem} omits {contract}')
    if 'inductive ContextualGlobalRuntimeSequence' not in source:
        raise ValueError('getter-aware GlobalIR expression sequence is missing')
    sequence_theorem = 'evaluate_contextualGlobalRuntimeSequence_preserves_type'
    begin_theorem = 'evaluate_contextualGlobalRuntimeBegin_preserves_type'
    terms_theorem = 'evaluate_contextualGlobalRuntimeTerms_preserves_type'
    runtime_call_theorem = 'evaluate_contextualGlobalRuntimeCall_preserves_type'
    runtime_closure_call_theorem = 'evaluate_contextualGlobalRuntimeClosureCall_preserves_type'
    let_many_theorem = 'evaluate_contextualGlobalRuntimeLetMany_preserves_type'
    optional_theorem = 'evaluate_contextualGlobalRuntimeIntegerOptionalCall_preserves_type'
    for theorem, dependency in ((sequence_theorem, runtime_theorem),
                                (begin_theorem, sequence_theorem),
                                (terms_theorem, runtime_theorem),
                                (runtime_call_theorem, terms_theorem),
                                (runtime_closure_call_theorem, terms_theorem),
                                (let_many_theorem, terms_theorem),
                                (optional_theorem, runtime_theorem)):
        start = source.find(f'theorem {theorem}')
        end = source.find('\ntheorem ', start + 8)
        body = source[start:end if end >= 0 else None]
        if start < 0 or dependency not in body:
            raise ValueError(f'{theorem} does not compose {dependency}')
    call_start = source.find(f'theorem {runtime_call_theorem}')
    call_end = source.find('\ntheorem ', call_start + 8)
    runtime_call = source[call_start:call_end if call_end >= 0 else None]
    for contract in ('argumentsTyping', 'argumentsSuccess', 'arity', 'bodyTyping',
                     'bodySuccess', 'storeLayout', 'storeTyped', 'callEq',
                     runtime_theorem):
        if contract not in runtime_call:
            raise ValueError(f'{runtime_call_theorem} omits {contract}')
    closure_start = source.find(f'theorem {runtime_closure_call_theorem}')
    closure_end = source.find('\ntheorem ', closure_start + 8)
    runtime_closure_call = source[closure_start:closure_end if closure_end >= 0 else None]
    for contract in ('capturedTyped', 'argumentsTyping', 'argumentsSuccess',
                     'arityAgreement', 'bodyTyping', 'bodySuccess',
                     'ValuesTyped.append',
                     'evaluate_closure_application_preserves_type_from_body_result',
                     runtime_theorem):
        if contract not in runtime_closure_call:
            raise ValueError(f'{runtime_closure_call_theorem} omits {contract}')
    if 'inductive ContextualGlobalRuntimeIntegerOptionalCall' not in source:
        raise ValueError('getter-aware Option integer operation typing is missing')


def verify_contextual_global_initializer_safety():
    """Pin the source-row to GlobalIR contextual initializer preservation path."""
    root = pathlib.Path(__file__).resolve().parents[1]
    source = (root / 'NLisp/GlobalProgramEntry.lean').read_text(encoding='utf-8')
    for theorem in ('ContextualGlobalInitializerRows.toTypesAgree',
                    'toRuntimeProgram_contextualGlobal_initialization_preserves_store'):
        if f'theorem {theorem}' not in source:
            raise ValueError(f'contextual GlobalIR initializer proof is missing: {theorem}')
    if 'GlobalIR.ContextualGlobalArithmeticTerm globals assignment []' not in source:
        raise ValueError('contextual initializer rows no longer carry global-call term evidence')
    if 'initializeValues_contextualGlobal_preserves_typed' not in source:
        raise ValueError('contextual initializer store theorem does not use GlobalIR preservation')


def verify_global_ir_error_correspondence():
    """Keep constructor fault propagation in the source/GlobalIR proof set."""
    root = pathlib.Path(__file__).resolve().parents[1]
    source = (root / 'NLisp/GlobalIRErrorCorrespondence.lean').read_text(
        encoding='utf-8')
    aggregate = (root / 'NLisp.lean').read_text(encoding='utf-8')
    if 'import NLisp.GlobalIRErrorCorrespondence' not in aggregate:
        raise ValueError('source/GlobalIR fault correspondence is not in NLisp.lean')
    for theorem in ('application_function_fault_propagates_to_globalIR',
                    'application_arguments_fault_propagates_to_globalIR',
                    'conditional_condition_fault_propagates_to_globalIR',
                    'some_child_fault_propagates_to_globalIR',
                    'cons_head_fault_propagates_to_globalIR',
                    'cons_tail_fault_propagates_to_globalIR',
                    'floatBin_left_fault_propagates_to_globalIR',
                    'floatBin_right_fault_propagates_to_globalIR',
                    'conditional_selected_branch_fault_propagates_to_globalIR',
                    'matchList_scrutinee_fault_propagates_to_globalIR',
                    'matchOption_scrutinee_fault_propagates_to_globalIR'):
        if f'theorem {theorem}' not in source:
            raise ValueError(f'source/GlobalIR fault propagation theorem missing: {theorem}')


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
    """Lower generic functions once; Lean checks the resulting polymorphic IR."""
    def __init__(self, document, **options):
        super().__init__(document, **options)
        self.declarations = document['declarations']
        self.function_globals = {name: data for name, data in self.globals.items() if data[3] is not None}
        self.value_globals = {name: data for name, data in self.globals.items() if data[3] is None}
        self.indices = {name: index for index, name in enumerate(self.function_globals)}
        self.variable_indices = {}
        self.global_ids = {}
        self.parameter_nodes = {}
        for declaration in document['declarations']:
            if atom(declaration[0]) == 'define':
                binding = declaration[1][0]
                self.global_ids[atom(binding)] = binding['token_identity']
            elif atom(declaration[0]) == 'defun':
                binding = declaration[1]
                self.global_ids[atom(binding)] = binding['token_identity']
                self.parameter_nodes[atom(binding)] = (
                    declaration[2] if len(declaration) == 5 else declaration[2][2])

    @staticmethod
    def binding(node, ty):
        return ('binding', natural(node['token_identity'], 'binder identity'), atom(node)), ty

    def is_scheme(self, node, ctx):
        name = atom(node)
        return name in self.schemes and node['resolved_identity'] == self.global_ids[name]

    def ty(self, ty):
        if isinstance(ty, str):
            if ty not in ('Integer', 'Boolean', 'Unit', 'Float', 'String', 'Character'):
                raise ValueError('type outside polymorphic operational model: ' + ty)
            return {'Integer': 'Ty.integer', 'Boolean': 'Ty.boolean', 'Unit': 'Ty.unit',
                    'Float': 'Ty.float', 'String': 'Ty.string',
                    'Character': 'Ty.character'}[ty]
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
            if self.globals[name][3] is None:
                raise ValueError(f'top-level value {name} requires a GlobalIR getter certificate')
            variables = self.schemes.get(name, [])
            if variables and substitutions is None:
                raise ValueError('polymorphic value needs explicit or inferred type arguments')
            arguments = [substitutions[v] for v in variables]
            actual = substitute_type(ty, substitutions) if variables else ty
            return f'(Expr.global {self.indices[name]} [{", ".join(self.ty(t) for t in arguments)}])', actual
        float_operations = {'float+': 'add', 'float-': 'sub',
                            'float*': 'mul', 'float/': 'div'}
        float_builtin_ids = {'float+': 39, 'float-': 42, 'float*': 45, 'float/': 48}
        if name in float_operations and selected == float_builtin_ids[name]:
            body = (f'(Expr.floatBin FloatBinOp.{float_operations[name]} '
                    '(Expr.var 0) (Expr.var 1))')
            return (f'(Expr.lam [Ty.float, Ty.float] Ty.float {body})',
                    ('Function', ('Float', 'Float'), 'Float'))
        comparison_bodies = {
            '<': '(Expr.ite (Expr.le (Expr.var 1) (Expr.var 0)) (Expr.bool false) (Expr.bool true))',
            '>': '(Expr.ite (Expr.le (Expr.var 0) (Expr.var 1)) (Expr.bool false) (Expr.bool true))',
            '>=': '(Expr.le (Expr.var 1) (Expr.var 0))',
        }
        comparison_ids = {'<': 12, '>': 18, '>=': 21}
        if name in comparison_bodies and selected == comparison_ids[name]:
            return (f'(Expr.lam [Ty.integer, Ty.integer] Ty.boolean {comparison_bodies[name]})',
                    ('Function', ('Integer', 'Integer'), 'Boolean'))
        if name == 'boolean=' and selected == 33:
            body = ('(Expr.ite (Expr.var 0) (Expr.var 1) '
                    '(Expr.ite (Expr.var 1) (Expr.bool false) (Expr.bool true)))')
            return (f'(Expr.lam [Ty.boolean, Ty.boolean] Ty.boolean {body})',
                    ('Function', ('Boolean', 'Boolean'), 'Boolean'))
        if name == 'not' and selected == 36:
            body = '(Expr.ite (Expr.var 0) (Expr.bool false) (Expr.bool true))'
            return (f'(Expr.lam [Ty.boolean] Ty.boolean {body})',
                    ('Function', ('Boolean',), 'Boolean'))
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
            if token.startswith('"'):
                characters = ', '.join(f'(Char.ofNat {ord(c)})' for c in decode_string(token))
                return f'(Expr.string (String.mk [{characters}]))', 'String'
            if token.startswith('#\\'):
                value = token[2:]
                if value in ('newline', 'space', 'tab'):
                    value = {'newline': '\n', 'space': ' ', 'tab': '\t'}[value]
                elif re.fullmatch(r'u\{[0-9a-fA-F]{1,6}\}', value):
                    value = unicode_scalar(int(value[2:-1], 16))
                if len(value) != 1:
                    raise ValueError('invalid character token')
                unicode_scalar(ord(value))
                return f'(Expr.character (Char.ofNat {ord(value)}))', 'Character'
            if re.fullmatch(r'-?[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?', token):
                literal = lean_string(token)
                parsed = f'(NLisp.Lexical.readFloatLiteral {literal})'
                return f'(Expr.float ({parsed}.get (by decide)))', 'Float'
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
        for name, (_, ty, body, parameters) in self.function_globals.items():
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
        source_entries = []
        global_value_section = ''
        if self.value_globals:
            for name, (_, ty, _body, parameters) in self.globals.items():
                identity = self.global_ids[name]
                if parameters is None:
                    self.type_variables = {}
                    self.variable_indices = {}
                    source_entries.append(
                        f'(.value {identity} {self.ty(ty)} (by simp [NLisp.Surface.Ty.wellFormed]) '
                        'NLisp.Surface.Expr.unit)')
                else:
                    function_index = self.indices[name]
                    source_entries.append(
                        f'(.function {identity} signatures[{function_index}] '
                        f'(by\n'
                        f'  have typedBodies := NLisp.Surface.elaborateProgram_typed all_bodies_check\n'
                        f'  have found : signatures[{function_index}]? = some signatures[{function_index}] := by simp [signatures, getElem?_def]\n'
                        f'  exact NLisp.Surface.BodiesHaveTypes.signature_valid_at typedBodies {function_index} '
                        f'    signatures[{function_index}] found) '
                        f'⟨{len(parameters)}, NLisp.PolyIR.erase bodies[{function_index}]⟩)')
            global_value_section = (
                f'def polySourceForms : List NLisp.CBindingWalk.Node := [{", ".join(binding_tree(form) for form in self.declarations)}]\n'
                f'def sourceEntrySeed : List NLisp.GlobalProgramEntry.Entry := [{", ".join(source_entries)}]\n'
                'def loweredSourceEntries := NLisp.GlobalSourceLowering.lowerAndReplaceValues 1024 sourceEntrySeed polySourceForms\n'
                'theorem loweredSourceEntries_ok : loweredSourceEntries.isSome = true := by native_decide\n'
                'def runtimeEntries := loweredSourceEntries.get loweredSourceEntries_ok\n'
                f'def globalIRRuntimeProgram := NLisp.GlobalProgramEntry.toRuntimeProgram runtimeEntries {self.globals["main"][0]}\n'
                'def initializerRowsAccepted := NLisp.GlobalProgramEntry.checkInitializerRows 1024 runtimeEntries\n'
                '  (NLisp.GlobalProgramEntry.valueTypes runtimeEntries) 0 runtimeEntries\n'
                'theorem initializerRowsAccepted_ok : initializerRowsAccepted = true := by native_decide\n'
                'def typedInitializerRows : NLisp.GlobalProgramEntry.TypedInitializerRows runtimeEntries\n'
                '    (NLisp.GlobalProgramEntry.valueTypes runtimeEntries) 0 runtimeEntries :=\n'
                '  (NLisp.GlobalProgramEntry.checkInitializerRows_sound 1024 runtimeEntries\n'
                '    (NLisp.GlobalProgramEntry.valueTypes runtimeEntries) 0 runtimeEntries\n'
                '    initializerRowsAccepted_ok).toTypedInitializerRows 1024 runtimeEntries\n'
                '      (NLisp.GlobalProgramEntry.valueTypes runtimeEntries) 0 runtimeEntries\n'
                'theorem globalIRInitializerTypesAgree :\n'
                '    NLisp.GlobalIR.InitializerTypesAgree (NLisp.GlobalProgramEntry.valueTypes runtimeEntries) 0\n'
                '      globalIRRuntimeProgram.initializers := by\n'
                '  exact typedInitializerRows.toRuntimeProgram_types_agree runtimeEntries globalIRRuntimeProgram.entry\n'
                'def globalIRInitialization := NLisp.GlobalIR.initializeValues globalIRRuntimeProgram.definitions\n'
                '  4096 (List.replicate globalIRRuntimeProgram.initializers.length none) 0\n'
                '  globalIRRuntimeProgram.initializers\n'
                'theorem globalIRInitialization_succeeds : globalIRInitialization.isOk = true := by native_decide\n'
                'theorem globalIRInitialization_store_typed :\n'
                '    (arithmeticRows : NLisp.GlobalProgramEntry.ArithmeticInitializerRows\n'
                '      (NLisp.GlobalProgramEntry.valueTypes runtimeEntries) 0 runtimeEntries) →\n'
                '    ∃ store, globalIRInitialization = .ok store ∧\n'
                '      NLisp.GlobalIR.StoreWellTyped signatures\n'
                '        (NLisp.GlobalProgramEntry.valueTypes runtimeEntries) store := by\n'
                '  intro arithmeticRows\n'
                '  cases initialized : globalIRInitialization with\n'
                '  | error fault =>\n'
                '      have successBool := globalIRInitialization_succeeds\n'
                '      rw [initialized] at successBool\n'
                '      simp [Except.isOk, Except.toBool] at successBool\n'
                '  | ok store =>\n'
                '      refine ⟨store, rfl, ?_⟩\n'
                '      apply NLisp.GlobalProgramEntry.TypedInitializerRows.toRuntimeProgram_initialization_preserves_store_arithmetic\n'
                '        runtimeEntries signatures globalIRRuntimeProgram.entry 4096 store\n'
                '        typedInitializerRows arithmeticRows\n'
                '      simpa [globalIRInitialization] using initialized\n')
        return ('import NLisp\nopen NLisp.Surface\nnamespace VerifiedPolyProgram\n'
                f'def signatures : List Signature := [{", ".join(signatures)}]\n'
                f'def bodies : List Expr := [{", ".join(bodies)}]\n'
                'def checked := elaborateProgram 512 signatures bodies\n'
                'theorem all_bodies_check : checked.isSome = true := by decide\n'
                'def program : NLisp.PolyIR.Program := checked.get all_bodies_check\n'
                'def source : Definitions := signatures.zip bodies\n'
                'theorem program_erasure : program.erase = NLisp.PolyIR.eraseDefinitions source := by rfl\n'
                'def globalIRGlobals : List Signature := NLisp.GlobalIR.assembleGlobals source []\n'
                'def globalIRDefinitions : List NLisp.GlobalIR.Definition := NLisp.GlobalIR.assembleProgram source []\n'
                'def globalIRChecked := elaborateDefinitions 512 globalIRGlobals signatures bodies\n'
                'theorem globalIRGlobals_eq : globalIRGlobals = signatures := by\n'
                '  have bodyTypes := NLisp.Surface.elaborateProgram_typed all_bodies_check\n'
                '  have bodyLengths := bodyTypes.length_eq\n'
                '  change (signatures.zip bodies).map Prod.fst ++ [] = signatures\n'
                '  rw [NLisp.GlobalIR.map_fst_zip_eq_left signatures bodies bodyLengths]\n'
                '  simp\n'
                'theorem globalIRChecked_ok : globalIRChecked.isSome = true := by\n'
                '  unfold globalIRChecked\n'
                '  rw [globalIRGlobals_eq]\n'
                '  simpa [elaborateProgram] using all_bodies_check\n'
                'theorem globalIR_layout_typed :\n'
                '    NLisp.GlobalIR.GlobalProgramTyped globalIRGlobals source []\n'
                '      (NLisp.GlobalIR.functionSourcesFor source.length) globalIRDefinitions :=\n'
                '  NLisp.GlobalIR.assembleProgram_typed_of_elaborated 512 signatures bodies []\n'
                '    globalIRChecked_ok (by\n'
                '      intro slot type found\n'
                '      have impossible : ¬ slot < ([] : List Ty).length := by simp\n'
                '      simp only [getElem?_def, dif_neg impossible] at found)\n'
                f'{global_value_section}'
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
                      'typed GlobalIR function/getter layout for programs without top-level values',
                      'value declaration initializer row typing and successful GlobalIR initialization when present',
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
                'theorem source_static_call_chain_terminates (chain : Nat → Nat)\n'
                '    (step : ∀ index, NLisp.MacroTermination.Calls certificate.edges\n'
                '      (chain (index + 1)) (chain index)) : False :=\n'
                '  NLisp.ProcessCertificate.source_static_call_chain_terminates certificate chain step\n'
                'theorem source_static_call_chain_length_bounded (chain : Nat → Nat)\n'
                '    (step : ∀ index, NLisp.MacroTermination.Calls certificate.edges\n'
                '      (chain (index + 1)) (chain index)) (count : Nat) :\n'
                '    count + NLisp.MacroTermination.rank certificate.ranks (chain count) ≤\n'
                '      NLisp.MacroTermination.rank certificate.ranks (chain 0) :=\n'
                '  NLisp.ProcessCertificate.source_static_call_chain_length_bounded certificate chain step count\n'
                'end VerifiedNLispSource\n')
    fuel = 4 * syntax_nodes(document['declarations']) + 4
    return ('\nnamespace VerifiedNLispSource\n'
            'def certificate : NLisp.ProcessCertificate.CheckedExpansion := {\n'
            '  toCheckedSource := CSourceCorrespondence.checked,\n'
            '  expanded := CExpansionCorrespondence.expanded, annotated := CProgramScope.forms,\n'
            f'  scopeFuel := {fuel}, localCertificate := CExpansionCorrespondence.programCertificate,\n'
            '  localCertificate_source := by rfl, localCertificate_target := by rfl,\n'
            '  localCertificate_fresh := CExpansionCorrespondence.program_certificate_fresh_accepted,\n'
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
            'theorem source_expands_with_scopes_and_freshness :\n'
            '  certificate.text.toUTF8.data.data = certificate.bytes ∧\n'
            '  NLisp.SourceReader.readWithFuel certificate.lexFuel certificate.parseFuel certificate.text = some certificate.parsed ∧\n'
            '  NLisp.SourceReader.normalize certificate.parsed = some certificate.normalized ∧\n'
            '  NLisp.CExpansion.Expands (NLisp.CExpansion.sourceRules 0 certificate.normalized)\n'
            '    (.list (NLisp.CExpansion.programForms certificate.normalized)) (.list certificate.expanded) ∧\n'
            '  NLisp.CExpansion.disjointIntervals\n'
            '    (NLisp.ExpansionCertificate.freshIntervals certificate.localCertificate) = true ∧\n'
            '  certificate.annotated.map NLisp.CBindingWalk.Node.erase = certificate.expanded ∧\n'
            '  ∃ sites, NLisp.CBindingWalk.references certificate.scopeFuel certificate.annotated\n'
            '      NLisp.CBindingWalk.builtinEnvironment = some sites ∧\n'
            '    ∀ site ∈ sites, NLisp.CBindingWalk.Corresponds site :=\n'
            '  NLisp.ProcessCertificate.source_expands_with_scopes_and_freshness certificate\n'
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
        source_decode_fuel = max(
            (syntax_nodes(declaration) for declaration in document['declarations']), default=0) + 1
        source_header_parts = []
        source_body_parts = []
        decoded_definition_terms = []
        body_exact_theorems = []
        for index in range(len(exporter.function_globals)):
            source_header_parts.append(
                f'def sourceHeader{index} : NLisp.ExpansionLowering.Header := decodedHeaders[{index}]\' (by decide)\n')
            concrete_headers = ', '.join(f'sourceHeader{i}' for i in range(len(exporter.function_globals)))
            raw_body_expression = (f'NLisp.Named.decodeExpr {source_decode_fuel} [{concrete_headers}] '
                                   f'sourceHeader{index}.body')
            source_body_parts.extend([
                f'theorem sourceRawBody{index}_ok : ({raw_body_expression}).isSome = true := by rfl\n',
                f'def sourceBody{index} := ({raw_body_expression}).get sourceRawBody{index}_ok\n',
                f'theorem sourceRawBody{index}_exact : {raw_body_expression} = some sourceBody{index} :=\n'
                f'  (Option.some_get sourceRawBody{index}_ok).symm\n',
            ])
            body_exact_theorems.append(f'sourceRawBody{index}_exact')
            decoded_definition_terms.append(
                f'(sourceHeader{index}.parameters.map Prod.fst, sourceBody{index})')
        decoder_definitions = ', '.join(decoded_definition_terms)
        body_simp_theorems = ', '.join(body_exact_theorems)
        function_forms = ', '.join(binding_tree(form) for form in document['declarations']
                                   if atom(form[0]) == 'defun')
        poly_proof_sections = [
            '\nnamespace VerifiedPolyProgram\n',
            f'def functionForms : List NLisp.CBindingWalk.Node := [{function_forms}]\n',
            'theorem source_lowering_checked :\n',
            '    NLisp.ExpansionLowering.checkProgram 512 functionForms signatures bodies = true := by native_decide\n',
            f'theorem main_is_entry : NLisp.ExpansionLowering.checkMain 512 functionForms {exporter.indices["main"]} = true := by decide\n',
            'theorem program_typed : NLisp.PolyIR.ProgramTyped signatures source :=\n',
            '  NLisp.Surface.elaborateProgram_programTyped all_bodies_check\n',
            'theorem entry_has_no_type_error (fuel : Nat) (fault : NLisp.PolyIR.Fault)\n',
            '    (h : NLisp.PolyIR.evaluate program.erase fuel [] (NLisp.PolyIR.erase entry) = .error fault) :\n',
            '    fault = .outOfFuel := by\n',
            '  rw [program_erasure] at h\n',
            '  exact NLisp.PolyIR.evaluation_no_type_error program_typed\n',
            '    (NLisp.Surface.elaborate_typed entry_checks)\n',
            '    (assignment := fun _ => Ty.unit) (by simpa only [NLisp.Surface.interpretTypes] using NLisp.PolyIR.ValuesTyped.nil) h\n',
            f'def decoded := NLisp.Named.decodeTopLevelProgram {source_decode_fuel} CProgramScope.forms\n',
            f'def sourceProgramHeaders := NLisp.ExpansionLowering.readProgramHeaders {source_decode_fuel} 0 CProgramScope.forms\n',
            'theorem sourceHeaders_ok : sourceProgramHeaders.isSome = true := by decide\n',
            'def decodedHeaders := (sourceProgramHeaders.get sourceHeaders_ok).functions\n',
            ''.join(source_header_parts),
            f'theorem sourceHeaders_concrete : decodedHeaders = [{", ".join(f"sourceHeader{i}" for i in range(len(exporter.function_globals)))}] := by rfl\n',
            ''.join(source_body_parts),
            f'def decodedSourceDefinitions : NLisp.Named.Definitions := [{decoder_definitions}]\n',
            'theorem sourceFunctions_decoded :\n',
            f'    NLisp.Named.decodeFunctionsRaw {source_decode_fuel} decodedHeaders decodedHeaders = some decodedSourceDefinitions := by\n',
            '  rw [sourceHeaders_concrete]\n',
            f'  simp [NLisp.Named.decodeFunctionsRaw, decodedSourceDefinitions, {body_simp_theorems}]\n',
            'theorem source_decodes : decoded.isSome = true := by decide\n',
            'def namedSource : NLisp.Named.Definitions := (decoded.get source_decodes).1\n',
            'theorem lowered_source_matches : NLisp.Named.lowerDefinitions namedSource = program.erase := by rfl\n',
            f'def namedEntry : NLisp.Named.Expr := .app (.global {exporter.indices["main"]}) []\n',
            'theorem source_evaluation_preserved {value : NLisp.Named.Value}\n',
            '    (h : NLisp.Named.Evaluates namedSource [] namedEntry value) :\n',
            '    NLisp.PolyIR.Evaluates program.erase [] (NLisp.PolyIR.erase entry) (NLisp.Named.lowerValue value) := by\n',
            '  have preserved := NLisp.Named.evaluation_preserved h\n',
            '  simpa [lowered_source_matches, namedEntry, entry, NLisp.Named.lowerEnv,\n',
            '    NLisp.Named.lower, NLisp.Named.identities] using preserved\n',
            'end VerifiedPolyProgram\n',
        ]
        proof += ''.join(poly_proof_sections)
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
        verify_builtin_table()
        verify_c_type_argument_call_inference()
        verify_integer_division_semantics()
        verify_macro_copy_binder_composition()
        verify_checker_full_cost_contract()
        verify_c_utf8_reader()
        verify_c_binary64_contract()
        verify_c_value_slot_runtime()
        verify_mixed_top_level_declaration_order()
        verify_global_ir_closure_application_safety()
        verify_contextual_global_initializer_safety()
        verify_global_ir_error_correspondence()
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
