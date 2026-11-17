"""Regression tests for recursive groups and bounded recursive macro expansion."""
import pathlib
import subprocess
import sys
import tempfile
import unittest

NLISP = str(pathlib.Path(sys.argv.pop(1)).resolve())


def macro(name, body, args=()):
    pattern = ' '.join((name, *args))
    contracts = ' '.join(f'({arg} (Syntax Integer))' for arg in args)
    return f'(define-macro {name} (syntax-rules/typed (({pattern}) ({contracts}) (Syntax Integer) {body})))'


class Syntax(unittest.TestCase):
    def process(self, source, command='check', limits=()):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / 'syntax.nlisp'
            path.write_text(source, encoding='utf-8')
            return subprocess.run([NLISP, command, str(path), *limits], capture_output=True, text=True, timeout=10)

    def expect_run(self, source, expected):
        result = self.process(source, 'run')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), str(expected))

    def expect_rejected(self, source, status, message):
        result = self.process(source)
        self.assertEqual(result.returncode, status, result.stderr)
        self.assertIn(message, result.stderr)

    def test_defrec_monomorphic_and_polymorphic(self):
        self.expect_run('''
(defrec
 ((even ((n Integer)) Boolean (if (integer= n 0) true (odd (- n 1))))
  (odd ((n Integer)) Boolean (if (integer= n 0) false (even (- n 1))))))
(defun main () Integer (if (even 20) 42 0))
''', 42)
        self.expect_run('''
(defrec
 ((identity (forall (T) ((x T)) T) x)
  (apply-id (forall (U) ((x U)) U) (identity x))))
(defun main () Integer (apply-id 42))
''', 42)

    def test_defrec_validation(self):
        for group in ('(defrec ())', '(defrec)', '(defrec 42)', '(defrec (42))',
                      '(defrec ((f () Integer)))'):
            with self.subTest(group=group):
                self.expect_rejected(group + '\n(defun main () Integer 0)', 4, 'defrec' if group != '(defrec ((f () Integer)))' else 'forall')
        self.expect_rejected('''
(defrec ((f () Integer 1) (f () Integer 2)))
(defun main () Integer (f))
''', 5, 'duplicate name')
        self.expect_rejected('(defrec ((main () Boolean true)))', 5, 'program requires main')

    def test_multiple_arities_and_nested_calls(self):
        source = '''
(define-macro sum
 (syntax-rules/typed
  ((sum) () (Syntax Integer) 0)
  ((sum x) ((x (Syntax Integer))) (Syntax Integer) x)
  ((sum x y) ((x (Syntax Integer)) (y (Syntax Integer))) (Syntax Integer) (+ x y))))
'''
        self.expect_run(source + '(defun main () Integer (sum (sum 40) (sum 2 (sum))))', 42)
        self.expect_rejected(source + '(defun main () Integer (sum 1 2 3))', 5, 'no macro rule')
        self.expect_rejected(source + '(defun main () Integer (sum true))', 5, 'macro input contract')

    def test_duplicate_arity_and_declaration(self):
        self.expect_rejected('''
(define-macro m (syntax-rules/typed
 ((m x) ((x (Syntax Integer))) (Syntax Integer) x)
 ((m y) ((y (Syntax Integer))) (Syntax Integer) y)))
(defun main () Integer 0)
''', 5, 'duplicate macro rule arity')
        self.expect_rejected(macro('m', '1') + macro('m', '2') + '(defun main () Integer 0)', 5, 'duplicate macro name')

    def test_rules_can_have_different_contracts(self):
        self.expect_run('''
(define-macro choose (syntax-rules/typed
 ((choose) () (Syntax Integer) 40)
 ((choose x) ((x (Syntax Boolean))) (Syntax Boolean) (not x))
 ((choose x y) ((x (Syntax Integer)) (y (Syntax Integer))) (Syntax Integer) (+ x y))))
(defun main () Integer (if (choose false) (choose (choose) 2) 0))
''', 42)

    def test_forward_calls_and_definition_site_scope(self):
        self.expect_run('(defun main () Integer (later 42))' + macro('later', 'x', ('x',)), 42)
        source = macro('first', '(later x)', ('x',))
        source += '(define (offset Integer) 40)'
        source += macro('later', '(+ offset x)', ('x',))
        source += '''
(defun main () Integer
 (let (((offset Integer) 9000)
       ((+ (Function (Integer Integer) Integer)) (lambda ((a Integer) (b Integer)) Integer 9999)))
   (first 2)))'''
        self.expect_run(source, 42)

    def test_unused_recursive_macros_are_accepted(self):
        sources = [macro('m', '(m x)', ('x',)),
                   macro('a', '(b x)', ('x',)) + macro('b', '(a x)', ('x',)),
                   macro('a', '(b x)', ('x',)) + macro('b', '(c x)', ('x',)) + macro('c', '(a x)', ('x',)),
                   '''(define-macro m (syntax-rules/typed
                     ((m) () (Syntax Integer) 0)
                     ((m x) ((x (Syntax Integer))) (Syntax Integer) (m))))''']
        for source in sources:
            with self.subTest(source=source):
                self.expect_run(source + '(defun main () Integer 42)', 42)

    def test_recursive_macro_expansion_can_terminate(self):
        self.expect_run('''
(define-macro m (syntax-rules/typed
 ((m) () (Syntax Integer) 42)
 ((m x) ((x (Syntax Integer))) (Syntax Integer) (+ x (m)))))
(defun main () Integer (m 0))
''', 42)
        source = macro('a', '42')
        # Add an arity-one rule to the same declaration rather than redefine it.
        source = '''(define-macro a (syntax-rules/typed
          ((a) () (Syntax Integer) 42)
          ((a x) ((x (Syntax Integer))) (Syntax Integer) (b))))'''
        source += macro('b', '(a)') + '(defun main () Integer (a 0))'
        self.expect_run(source, 42)

    def test_nonterminating_expansion_is_unknown_with_no_output(self):
        source = macro('forever', '(forever)') + '(defun main () Integer (forever))'
        for command in ('check', 'run', 'expand', 'export-core'):
            with self.subTest(command=command):
                result = self.process(source, command, ('--max-expansions', '5'))
                self.assertEqual(result.returncode, 7, result.stderr)
                self.assertEqual(result.stdout, '')
                self.assertIn('Unknown', result.stderr)
                self.assertIn('macro expansion limit', result.stderr)
        result = self.process(source)
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertIn('depth limit', result.stderr)

    def test_budget_boundaries(self):
        source = '(defun main () Integer 42)'
        for option, insufficient, sufficient in (
            ('--max-check-steps', '1', '2'),
            ('--max-generated-nodes', '5', '6'),
            ('--max-expansion-depth', '1', '2'),
        ):
            with self.subTest(option=option):
                result = self.process(source, limits=(option, insufficient))
                self.assertEqual(result.returncode, 7, result.stderr)
                self.assertEqual(result.stdout, '')
                result = self.process(source, limits=(option, sufficient))
                self.assertEqual(result.returncode, 0, result.stderr)
        recursive = '''(define-macro m (syntax-rules/typed
          ((m) () (Syntax Integer) 42)
          ((m x) ((x (Syntax Integer))) (Syntax Integer) (m))))
          (defun main () Integer (m 0))'''
        self.assertEqual(self.process(recursive, limits=('--max-expansions', '1')).returncode, 7)
        self.assertEqual(self.process(recursive, limits=('--max-expansions', '2')).returncode, 0)

    def test_invalid_limits_are_usage_errors(self):
        for value in ('-1', 'abc', '999999999999999999999999999999999999'):
            self.assertEqual(self.process('(defun main () Integer 42)', limits=('--max-expansions', value)).returncode, 2)
        self.assertEqual(self.process('(defun main () Integer 42)', limits=('--max-expansion-depth', '513')).returncode, 2)

    def test_shared_expansion_cannot_evade_node_budget(self):
        source = macro('twice', '(+ x x)', ('x',))
        expression = '1'
        for _ in range(12):
            expression = f'(twice {expression})'
        result = self.process(source + f'(defun main () Integer {expression})',
                              'export-core', ('--max-generated-nodes', '1000'))
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertEqual(result.stdout, '')

    def test_repeated_type_checks_are_bounded(self):
        expression = '1'
        for _ in range(15):
            expression = f'(twice {expression})'
        source = macro('twice', '(+ x x)', ('x',)) + f'(defun main () Integer {expression})'
        result = self.process(source, limits=('--max-check-steps', '5000'))
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertIn('type-check work limit', result.stderr)

    def test_every_rule_is_validated(self):
        self.expect_rejected('''
(define-macro m (syntax-rules/typed
 ((m) () (Syntax Integer) 42)
 ((m x) ((x (Syntax Integer))) (Syntax Integer) true)))
(defun main () Integer (m))
''', 5, 'macro definition output')

    def test_forward_macro_cannot_read_uninitialized_value(self):
        source = macro('first', '(later)') + '(define (early Integer) (first))'
        source += '(define (offset Integer) 42)' + macro('later', 'offset')
        source += '(defun main () Integer early)'
        self.expect_rejected(source, 5, 'before its initialization')


if __name__ == '__main__':
    unittest.main()
