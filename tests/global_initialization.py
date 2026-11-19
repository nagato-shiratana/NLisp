"""Shared global cells, eager initialization and escaped closures."""
import pathlib
import subprocess
import sys
import tempfile
import unittest

NLISP = str(pathlib.Path(sys.argv.pop(1)).resolve())


class GlobalInitialization(unittest.TestCase):
    def run_source(self, text, expected=None, error=None):
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / 'input.nlisp'
            source.write_text(text, encoding='utf-8')
            checked = subprocess.run([NLISP, 'check', str(source)], capture_output=True, encoding='utf-8')
            self.assertEqual(checked.returncode, 0, checked.stderr)
            result = subprocess.run([NLISP, 'run', str(source)], capture_output=True, encoding='utf-8')
            if error is None:
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), str(expected))
            else:
                self.assertEqual(result.returncode, 6, result.stderr)
                self.assertIn(error, result.stderr)

    def test_escaped_closure_sees_later_initialized_cell(self):
        self.run_source('''
(define (early (Function () Integer)) (make))
(define (offset Integer) 42)
(defun make () (Function () Integer) (lambda () Integer offset))
(defun main () Integer (early))
''', 42)

    def test_escaped_closure_retains_local_shadow(self):
        self.run_source('''
(define (early (Function () Integer)) (make))
(define (offset Integer) 42)
(defun make () (Function () Integer)
  (let (((offset Integer) 10)) (lambda () Integer offset)))
(defun main () Integer (early))
''', 10)

    def test_read_during_initialization_is_rejected(self):
        self.run_source('''
(define (early Integer) (read-offset))
(define (offset Integer) 42)
(defun read-offset () Integer offset)
(defun main () Integer early)
''', error='before its initialization')

    def test_unselected_branch_does_not_read_future_cell(self):
        self.run_source('''
(define (early Integer) (choose false))
(define (offset Integer) 42)
(defun choose ((take Boolean)) Integer (if take offset 7))
(defun main () Integer early)
''', 7)

    def test_unused_initializer_is_still_eager(self):
        self.run_source('''
(define (unused Integer) (read-offset))
(define (offset Integer) 42)
(defun read-offset () Integer offset)
(defun main () Integer 42)
''', error='before its initialization')

    def test_definition_site_macro_keeps_its_global(self):
        self.run_source('''
(define (offset Integer) 40)
(define-macro answer (syntax-rules/typed
  ((answer n) ((n (Syntax Integer))) (Syntax Integer) (+ offset n))))
(define (early (Function () Integer)) (make))
(define (later Integer) 999)
(defun make () (Function () Integer)
  (let (((offset Integer) 0)) (lambda () Integer (answer 2))))
(defun main () Integer (early))
''', 42)


if __name__ == '__main__':
    unittest.main()
