"""Check positive Lean ranking proofs and conservative Unknown outcomes."""
import copy
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
spec = importlib.util.spec_from_file_location('verify_lean', ROOT / 'tools/verify_lean.py')
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)
BUDGET = dict(max_certificate_bytes=4194304, max_conversion_steps=100000)


class MacroTermination(unittest.TestCase):
    def syntax(self, source):
        result = subprocess.run([NLISP, 'export-syntax', str(source), '--max-expansions', '0'],
                                capture_output=True, text=True, check=True)
        return json.loads(result.stdout)

    def cli(self, *arguments):
        return subprocess.run([sys.executable, str(ROOT / 'tools/verify_lean.py'), *map(str, arguments),
                               '--nlisp', NLISP, '--lake', LAKE], cwd=ROOT,
                              capture_output=True, text=True, timeout=30)

    def lean(self, proof):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / 'Rank.lean'
            path.write_text('import NLisp\nset_option maxRecDepth 4096\n' + proof)
            return subprocess.run([LAKE, 'env', 'lean', str(path)], cwd=ROOT,
                                  capture_output=True, text=True, timeout=30)

    def test_arity_decreases_and_certificate_replays_without_source(self):
        data = (ROOT / 'examples/recursive_expansion.nlisp').read_bytes()
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / 'arity.nlisp'
            source.write_bytes(data)
            document = self.syntax(source)
            plan = bridge.termination_plan(document)
            self.assertEqual(plan['status'], 'proved')
            self.assertEqual(plan['ranks'], [0, 1])
            certificate = pathlib.Path(directory) / 'Termination.lean'
            result = self.cli(source, '--mode', 'termination', '--max-expansions', 0,
                              '--output', certificate)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            manifest, proof = bridge.unpack_bundle(certificate.read_text())
            self.assertEqual(manifest['conversion']['mode'], 'termination')
            self.assertIn('well-founded static macro call graph', manifest['assurance']['kernel_checks'])
            self.assertIn('rule_calls_wellFounded', proof)
            self.assertIn('every_call_chain_bounded', proof)
            self.assertNotIn('expandedProgram', proof)
            source.unlink()
            result = self.cli('--verify-certificate', certificate)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_mutual_names_can_have_decreasing_rule_ranks(self):
        text = '''
(define-macro a (syntax-rules/typed
 ((a) () (Syntax Integer) 42)
 ((a x) ((x (Syntax Integer))) (Syntax Integer) (b))))
(define-macro b (syntax-rules/typed ((b) () (Syntax Integer) (a))))
(defun main () Integer (a 0))
'''
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / 'mutual.nlisp'
            source.write_text(text)
            document = self.syntax(source)
            proof, _ = bridge.render_proof(document, 'termination', BUDGET)
            plan = bridge.termination_plan(document)
            self.assertEqual(plan['ranks'], [0, 2, 1])
            result = self.lean(proof.removeprefix('import NLisp\n'))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_cycles_are_unknown_and_previous_artifact_is_preserved(self):
        sources = [
            '(define-macro forever (syntax-rules/typed ((forever) () (Syntax Integer) (forever))))',
            '''(define-macro a (syntax-rules/typed ((a) () (Syntax Integer) (b))))
               (define-macro b (syntax-rules/typed ((b) () (Syntax Integer) (a))))''',
        ]
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / 'cycle.nlisp'
            certificate = pathlib.Path(directory) / 'Previous.lean'
            certificate.write_bytes(b'previous valid artifact\n')
            for prefix in sources:
                source.write_text(prefix + '\n(defun main () Integer 42)')
                result = self.cli(source, '--mode', 'termination', '--max-expansions', 0,
                                  '--output', certificate)
                self.assertEqual(result.returncode, 7, result.stdout + result.stderr)
                self.assertIn('Unknown', result.stderr)
                self.assertIn('no decreasing rank', result.stderr)
                self.assertEqual(certificate.read_bytes(), b'previous valid artifact\n')

    def test_dynamic_head_is_unknown(self):
        text = '''
(define-macro apply (syntax-rules/typed
 ((apply f x) ((f (Syntax (Function (Integer) Integer))) (x (Syntax Integer)))
  (Syntax Integer) (f x))))
(defun main () Integer (apply (lambda ((x Integer)) Integer x) 42))
'''
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / 'dynamic.nlisp'
            source.write_text(text)
            document = self.syntax(source)
            self.assertEqual(bridge.termination_plan(document)['status'], 'unknown')
            with self.assertRaisesRegex(bridge.UnknownResult, 'head position'):
                bridge.render_proof(document, 'termination', BUDGET)

    def test_wrong_ranks_are_rejected_by_lean(self):
        document = self.syntax(ROOT / 'examples/recursive_expansion.nlisp')
        plan = bridge.termination_plan(document)
        plan['ranks'] = [0, 0]
        proof = (bridge.source_correspondence_proof(document) +
                 bridge.termination_correspondence_proof(document, plan, standalone=True))
        result = self.lean(proof)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('false', result.stdout + result.stderr)

    def test_omitted_dependency_is_rejected_by_lean(self):
        document = self.syntax(ROOT / 'examples/recursive_expansion.nlisp')
        plan = copy.deepcopy(bridge.termination_plan(document))
        plan['edges'] = []
        plan['ranks'] = [0, 0]
        result = self.lean(bridge.source_correspondence_proof(document) +
                           bridge.termination_correspondence_proof(document, plan, standalone=True))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('false', result.stdout + result.stderr)

    def test_unknown_static_analysis_does_not_reject_finite_expansion(self):
        text = '''
(define-macro unused-loop (syntax-rules/typed
 ((unused-loop) () (Syntax Integer) (unused-loop))))
(defun main () Integer 42)
'''
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / 'unused.nlisp'
            certificate = pathlib.Path(directory) / 'Finite.lean'
            source.write_text(text)
            result = self.cli(source, '--output', certificate)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            manifest, proof = bridge.unpack_bundle(certificate.read_text())
            event = manifest['conversion']['events'][-1]
            self.assertEqual(event['stage'], 'macro_termination')
            self.assertEqual(event['status'], 'unknown')
            self.assertIn('program_expands', proof)
            self.assertNotIn('rule_calls_wellFounded', proof)


if __name__ == '__main__':
    unittest.main()
