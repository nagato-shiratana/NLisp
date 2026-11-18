"""Verifier control-flow checks; kernel proofs are checked by Lean separately."""
import importlib.util
import pathlib
import tempfile
import types
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('bridge', ROOT / 'tools/verify_lean.py')
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)


class IndependentCertificate(unittest.TestCase):
    def make_bundle(self, directory, source=b'(defun main () Integer 42)', document_source=None):
        document = {'format': 'nlisp-scoped-expansion-v2',
                    'source_text': source.decode() if document_source is None else document_source,
                    'limits': dict(bridge.C_LIMITS)}
        proof, events = 'import NLisp\n', []
        limits = {'max_certificate_bytes': 4194304, 'max_conversion_steps': 100000}
        path = pathlib.Path(directory) / 'certificate.lean'
        path.write_bytes(bridge.pack_bundle(source, document, events, proof, 'core', limits).encode('utf-8'))
        args = types.SimpleNamespace(independent=True, nlisp='MUST_NOT_EXECUTE', lake='lake', **limits,
                                    **{name: None for name in bridge.C_LIMITS})
        return path, args, proof, events

    def test_no_c_process_is_executed(self):
        with tempfile.TemporaryDirectory() as directory:
            path, args, proof, events = self.make_bundle(directory)
            with mock.patch.object(bridge, 'run_export', side_effect=AssertionError('C replay forbidden')):
                with mock.patch.object(bridge, 'render_proof', return_value=(proof, events)):
                    with mock.patch.object(bridge, 'verify_certificate') as kernel:
                        self.assertEqual(bridge.replay_bundle(path, args), 'core')
                        kernel.assert_called_once()
                        self.assertFalse(kernel.call_args.kwargs['publish'])

    def test_source_mismatch_is_rejected_before_kernel(self):
        with tempfile.TemporaryDirectory() as directory:
            path, args, _, _ = self.make_bundle(directory, document_source='different source')
            with mock.patch.object(bridge, 'verify_certificate') as kernel:
                with self.assertRaisesRegex(ValueError, 'source bytes differ'):
                    bridge.replay_bundle(path, args)
                kernel.assert_not_called()

    def test_regenerated_body_must_match(self):
        with tempfile.TemporaryDirectory() as directory:
            path, args, _, events = self.make_bundle(directory)
            with mock.patch.object(bridge, 'render_proof', return_value=('different proof', events)):
                with mock.patch.object(bridge, 'verify_certificate') as kernel:
                    with self.assertRaisesRegex(ValueError, 'Lean body does not match'):
                        bridge.replay_bundle(path, args)
                    kernel.assert_not_called()


if __name__ == '__main__':
    unittest.main()
