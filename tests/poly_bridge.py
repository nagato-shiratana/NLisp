"""Integration checks for shared generic bodies and certificate-only replay."""
import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
NLISP = str(pathlib.Path(sys.argv.pop(1)).resolve())
LAKE = str(pathlib.Path(sys.argv.pop(1)).resolve())
spec = importlib.util.spec_from_file_location('bridge', ROOT / 'tools/verify_lean.py')
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)


class PolymorphicBridge(unittest.TestCase):
    def test_generic_program_and_independent_recheck(self):
        with tempfile.TemporaryDirectory() as directory:
            for example, expected_bodies in [('polymorphism', 4), ('polymorphic_recursion', 2),
                                              ('math_macros', 2)]:
                with self.subTest(example=example):
                    certificate = pathlib.Path(directory) / (example + '.lean')
                    command = [sys.executable, str(ROOT / 'tools/verify_lean.py'),
                               str(ROOT / 'examples' / (example + '.nlisp')), '--mode', 'poly',
                               '--nlisp', NLISP, '--lake', LAKE, '--output', str(certificate)]
                    result = subprocess.run(command, cwd=ROOT, capture_output=True,
                                            encoding='utf-8', timeout=180)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    manifest, proof = bridge.unpack_bundle(certificate.read_text(encoding='utf-8'))
                    programs = [event for event in manifest['conversion']['events']
                                if event['stage'] == 'generic_program']
                    self.assertEqual(len(programs), 1)
                    self.assertEqual(len(programs[0]['bodies']), expected_bodies)
                    self.assertIn('execution_erases', proof)
                    self.assertIn('source_lowering_checked', proof)
                    self.assertIn('lowered_source_matches', proof)
                    self.assertIn('source_evaluation_preserved', proof)
                    self.assertIn('entry_has_no_type_error', proof)
                    self.assertNotIn('Expr.fix', proof)
                    # The certificate checker must not start any C executable.
                    result = subprocess.run(
                        [sys.executable, str(ROOT / 'tools/verify_lean.py'), '--verify-certificate',
                         str(certificate), '--independent', '--nlisp', 'NO_SUCH_EXECUTABLE', '--lake', LAKE],
                        cwd=ROOT, capture_output=True, encoding='utf-8', timeout=180)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_top_level_captures_are_not_silently_reinterpreted(self):
        result = subprocess.run([NLISP, 'export-core', str(ROOT / 'examples/closure.nlisp')],
                                cwd=ROOT, capture_output=True, encoding='utf-8', check=True)
        document = json.loads(result.stdout)
        # Test a real declaration if present; insert a top-level value otherwise.
        if not any(bridge.atom(d[0]) == 'define' for d in document['declarations']):
            atom = lambda name: {'atom': name, 'origin': None}
            document['declarations'].insert(0, [atom('define'), [atom('x'), atom('Integer')], atom('1')])
        with self.assertRaisesRegex(ValueError, 'top-level captures'):
            bridge.PolyExporter(document)

    def test_kernel_rejects_type_correct_operation_change(self):
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / 'input.nlisp'
            source.write_text('(defun main () Integer (+ 40 2))', encoding='utf-8')
            result = subprocess.run([NLISP, 'export-core', str(source)],
                                    capture_output=True, encoding='utf-8', check=True)
            document = json.loads(result.stdout)
            proof, _ = bridge.render_proof(document, 'poly',
                {'max_certificate_bytes': 4194304, 'max_conversion_steps': 100000})
            altered = proof.replace('(Expr.add ', '(Expr.sub ', 1)
            self.assertNotEqual(proof, altered)
            output = pathlib.Path(directory) / 'Unrelated.lean'
            with self.assertRaises(subprocess.CalledProcessError):
                bridge.verify_certificate(altered, output, LAKE)
            self.assertFalse(output.exists())


if __name__ == '__main__':
    unittest.main()
