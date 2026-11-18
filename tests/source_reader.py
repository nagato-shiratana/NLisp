"""Independently read source and defrec normalization in Lean, including lexical edge cases."""
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


class SourceReader(unittest.TestCase):
    def document(self, data):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / 'input.nlisp'
            path.write_bytes(data)
            result = subprocess.run([NLISP, 'export-syntax', str(path)],
                                    capture_output=True, text=True, check=True)
        return json.loads(result.stdout)

    def lean(self, proof):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / 'Source.lean'
            path.write_text('import NLisp\nset_option maxRecDepth 4096\n'
                            'set_option maxHeartbeats 2000000\n' + proof)
            return subprocess.run([LAKE, 'env', 'lean', str(path)], cwd=ROOT,
                                  capture_output=True, text=True, timeout=60)

    def test_utf8_crlf_comments_quotes_and_delimiter_characters(self):
        text = r'''; Unicode comment: 読み取り
(define (text String) "quote: \" slash: \\ newline: \n unicode: \u{1f642} NUL: \u{0}")
(define (multiline String) "first
second")
(define (close Character) #\))
(define (open Character) #\()
(define (comment Character) #\;)
(define (quote Character) #\")
(define (space Character) #\space)
(define (newline Character) #\newline)
(define (tab Character) #\tab)
(define (nul Character) #\u{0})
(define (unicode Character) #\界)
(define (reservedText String) "#%nlisp1")
(defun main () Integer 42)
'''
        data = text.replace('\n', '\r\n').encode('utf-8')
        document = self.document(data)
        self.assertEqual(document['source_text'].encode('utf-8'), data)
        result = self.lean(bridge.source_correspondence_proof(document))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_defrec_normalization_matches_for_polymorphic_and_monomorphic_members(self):
        text = '''
(defrec ((identity (forall (T) ((x T)) T) x)
         (count ((n Integer)) Integer n)))
(defun main () Integer (identity (count 42)))
'''
        document = self.document(text.encode())
        self.assertEqual(len(document['source_ast']), 2)
        self.assertEqual(len(document['normalized_ast']), 3)
        result = self.lean(bridge.source_correspondence_proof(document))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_source_token_identity_tampering_is_rejected_by_lean(self):
        document = self.document(b'(defun main () Integer 42)')
        document['source_ast'][0][1]['token_identity'] += 3
        result = self.lean(bridge.source_correspondence_proof(document))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('false', result.stdout + result.stderr)

    def test_changed_source_text_is_rejected_by_lean(self):
        document = self.document(b'(defun main () Integer 42)')
        document['source_text'] = document['source_text'].replace('42', '43')
        result = self.lean(bridge.source_correspondence_proof(document))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('false', result.stdout + result.stderr)

    def test_changed_normalization_is_rejected_by_lean(self):
        document = self.document(b'(defrec ((main () Integer 42)))')
        changed = copy.deepcopy(document)
        changed['normalized_ast'][0][-1]['atom'] = '99'
        result = self.lean(bridge.source_correspondence_proof(changed))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('false', result.stdout + result.stderr)

    def test_invalid_literals_delimiters_reserved_names_and_nul_are_rejected(self):
        invalid = ['(', ')', '"unterminated', '"\\q"', '"\\u{d800}"',
                   '"\\u{1234567}"', '#\\ab', '#\\u{110000}', '#%nlisp1', ';\x00\n42']
        proof = '\n'.join(f'example : NLisp.SourceReader.read {bridge.lean_string(text)} = none := by decide'
                          for text in invalid)
        result = self.lean(proof)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_unicode_whitespace_matches_c_token_boundaries(self):
        values = list(range(9, 14)) + [0x20, 0x85, 0xa0, 0x1680] + list(range(0x2000, 0x200b)) + [0x2028, 0x2029, 0x202f, 0x205f, 0x3000]
        spaces = ''.join(map(chr, values))
        text = '; ignored\u2028(defun' + spaces + 'main' + spaces + '()' + spaces + 'Integer' + spaces + '42)'
        result = self.lean(bridge.source_correspondence_proof(self.document(text.encode('utf-8'))))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
