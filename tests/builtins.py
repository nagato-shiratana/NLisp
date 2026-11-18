"""Exercise every specified builtin through the source reader and evaluator."""
import pathlib
import inspect
import re
import subprocess
import sys
import tempfile
import unittest

EXECUTABLE = str(pathlib.Path(sys.argv.pop(1)).resolve())


class Builtins(unittest.TestCase):
    def test_specification_registration_and_coverage(self):
        root = pathlib.Path(__file__).resolve().parents[1]
        specification = (root / 'SPECIFICATION.md').read_text(encoding='utf-8').split('### 8.2')[1].split('### 8.3')[0]
        expected = set()
        for line in specification.splitlines():
            if line.startswith('| `'):
                expected.update(re.findall(r'`([^`]+)`', line.split('|')[1]))
        source = (root / 'src/nlisp.c').read_text(encoding='utf-8').split('static const BuiltinSpec builtin_specs[] = {')[1].split('};')[0]
        actual = re.findall(r'\{"([^"]+)"', source)
        self.assertEqual(set(actual), expected)
        self.assertEqual(len(actual), len(set(actual)))
        cases = inspect.getsource(self.test_all_builtins)
        for name in expected:
            self.assertIn('(' + name + ' ', cases, f'no source-level execution case for {name}')

    def run_expression(self, expression, expected):
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / 'case.nlisp'
            source.write_text(f'(defun main () Integer {expression})\n', encoding='utf-8')
            result = subprocess.run([EXECUTABLE, 'run', str(source)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), str(expected))

    def test_all_builtins(self):
        integer_cases = [
            ('(+ 9223372036854775807 1)', 9223372036854775808),
            ('(* 1000000000000000000000000 1000000000000000000000000)', 10**48),
            ('(match (quotient -9223372036854775808 -1) ((None) 0) ((Some n) n))', 9223372036854775808),
            ('(match (float-truncate 1.0e100) ((None) 0) ((Some n) n))', int(1.0e100)),
            ('(+ 20 22)', 42), ('(- 50 8)', 42), ('(* 6 7)', 42),
            ('(match (quotient -17 5) ((None) 999) ((Some n) n))', -3),
            ('(match (remainder -17 5) ((None) 999) ((Some n) n))', -2),
            ('(match (quotient 1 0) ((None) 42) ((Some n) n))', 42),
            ('(match (remainder 1 0) ((None) 42) ((Some n) n))', 42),
            ('(match (float-truncate -42.9) ((None) 999) ((Some n) n))', -42),
            ('(match (float-truncate (float/ 1.0 0.0)) ((None) 42) ((Some n) n))', 42),
            ('(match (float-truncate (float/ 0.0 0.0)) ((None) 42) ((Some n) n))', 42),
        ]
        boolean_cases = [
            '(not (< 2 1))', '(not (<= 3 2))', '(not (> 1 2))', '(not (>= 1 2))',
            '(not (integer= 41 42))', '(not (boolean= true false))', '(not (not true))',
            '(not (float< 2.0 1.0))', '(not (float<= 3.0 2.0))',
            '(not (float> 1.0 2.0))', '(not (float>= 1.0 2.0))',
            '(not (character= #\\a #\\b))',
            '(< 1 2)', '(<= 2 2)', '(> 3 2)', '(>= 2 2)', '(integer= 42 42)',
            '(boolean= true true)', '(not false)',
            '(float= (float+ 0.5 1.5) 2.0)',
            '(float= (float- 2.5 0.5) 2.0)',
            '(float= (float* 0.5 4.0) 2.0)',
            '(float= (float/ 4.0 2.0) 2.0)',
            '(float< 1.0 2.0)', '(float<= 2.0 2.0)',
            '(float> 3.0 2.0)', '(float>= 2.0 2.0)',
            '(float= (to-float 42) 42.0)',
            '(float= (to-float 9007199254740993) 9007199254740992.0)',
            '(float= (to-float 9007199254740995) 9007199254740996.0)',
            '(float= (to-float -9007199254740995) -9007199254740996.0)',
            '(not (float= (float/ 0.0 0.0) (float/ 0.0 0.0)))',
            '(string= (string-append "hello " "世界") "hello 世界")',
            '(string= "a\\u{0}b" (string-append "a\\u{0}" "b"))',
            '(not (string= "a\\u{0}b" "a\\u{0}c"))',
            '(string= "\\u{1f600}" "😀")',
            '(string= "\\n\\r\\t\\\"\\\\" "\\u{a}\\u{d}\\u{9}\\u{22}\\u{5c}")',
            '(character= #\\a #\\u{61})',
            '(character= #\\newline #\\u{a})',
            '(character= #\\space #\\u{20})',
            '(character= #\\tab #\\u{9})',
            '(character= #\\😀 #\\u{1f600})',
            '(character= #\\( #\\u{28})',
            '(character= #\\; #\\u{3b})',
        ]
        for expression, expected in integer_cases:
            with self.subTest(expression=expression):
                self.run_expression(expression, expected)
        for predicate in boolean_cases:
            with self.subTest(predicate=predicate):
                self.run_expression(f'(if {predicate} 42 0)', 42)

    def test_arbitrary_integer_rounding_and_division(self):
        for bits in (53, 54, 63, 100, 500, 1023):
            for offset in (-3, -1, 0, 1, 3):
                for sign in (-1, 1):
                    integer = sign * ((1 << bits) + offset)
                    expected = repr(float(integer))
                    with self.subTest(integer=integer):
                        self.run_expression(f'(if (float= (to-float {integer}) {expected}) 42 0)', 42)
        for left in (-10**100, -17, 0, 17, 10**100):
            for right in (-13, -1, 1, 13):
                q = abs(left) // abs(right) * (-1 if (left < 0) != (right < 0) else 1)
                remainder = left - q * right
                for name, expected in [('quotient', q), ('remainder', remainder)]:
                    with self.subTest(left=left, right=right, name=name):
                        self.run_expression(f'(match ({name} {left} {right}) ((None) 123) ((Some n) n))', expected)

    def test_reject_invalid_utf8(self):
        for invalid in (b'\xc0\xaf', b'\xed\xa0\x80', b'\xf4\x90\x80\x80', b'\x80', b'\x00'):
            with self.subTest(invalid=invalid), tempfile.TemporaryDirectory() as directory:
                source = pathlib.Path(directory) / 'case.nlisp'
                source.write_bytes(b'(defun main () Integer (begin "' + invalid + b'" 0))')
                result = subprocess.run([EXECUTABLE, 'check', str(source)], capture_output=True)
                self.assertEqual(result.returncode, 4, result.stderr)

    def test_reject_malformed_literals(self):
        for literal in ['"\\q"', '"\\u{d800}"', '"\\u{110000}"', '"\\u{}"',
                        '"unterminated', '#\\u{d800}', '#\\u{110000}', '#\\unknown']:
            with self.subTest(literal=literal), tempfile.TemporaryDirectory() as directory:
                source = pathlib.Path(directory) / 'case.nlisp'
                source.write_text(f'(defun main () Integer (begin {literal} 0))')
                result = subprocess.run([EXECUTABLE, 'check', str(source)], capture_output=True)
                self.assertEqual(result.returncode, 4, result.stderr)


if __name__ == '__main__':
    unittest.main()
