#!/usr/bin/env python3
"""Deterministic regressions for the Lean proof-escape lexical check."""
import runpy
import unittest
from pathlib import Path


class ProofEscapeTests(unittest.TestCase):
    def setUp(self):
        scanner = Path(__file__).with_name('check-proof-escapes.py')
        self.violations = runpy.run_path(str(scanner))['violations']

    def test_prose_and_comments(self):
        for source in [
            'def statement := "axes admit promotion"',
            '-- sorry admit native_decide bv_decide ofReduceBool axiom\nexample : True := by trivial',
            '/- outer sorry /- nested admit -/ native_decide -/\ndef value := 1',
            'def value := "axiom sorry ofReduceBool"',
        ]:
            with self.subTest(source=source):
                self.assertEqual(self.violations(source), [])

    def test_actual_forbidden_identifiers(self):
        for token in ['sorry', 'admit', 'native_decide', 'bv_decide', 'ofReduceBool']:
            for source in [f'example : True := by {token}', f'#check Lean.{token}']:
                with self.subTest(source=source):
                    self.assertIn((1, token), self.violations(source))
        self.assertIn((1, 'ofReduceBool'), self.violations('#check Lean.«ofReduceBool»'))

    def test_axiom_declarations(self):
        for source in ['axiom impossible : False', 'private axiom impossible : False',
                       'namespace N\naxiom impossible : False\nend N']:
            with self.subTest(source=source):
                self.assertTrue(any(token == 'axiom' for _, token in self.violations(source)))

    def test_raw_strings_and_following_code(self):
        for source in ['def value := r"axes admit promotion"',
                       'def value := r##"a quote " and sorry "# remain text"##',
                       'def value := r#"backslash \\"#']:
            with self.subTest(source=source):
                self.assertEqual(self.violations(source), [])
        self.assertIn((1, 'sorry'), self.violations('def value := r##"sorry"##; example := by sorry'))

    def test_escaped_quotes_and_following_code(self):
        source = r'def value := "text \" admit \\"; example := by sorry'
        self.assertEqual(self.violations(source), [(1, 'sorry')])
        source = r'def value := "line\n\"admit\""' + '\nexample := by admit'
        self.assertEqual(self.violations(source), [(2, 'admit')])

    def test_character_literals_and_primed_identifiers(self):
        source = r'''def chars := ['"', '\'', '\\', '\u0041', '{', '}']
def admit' := 1
def sorry' := admit'
example := by sorry'''
        self.assertEqual(self.violations(source), [(4, 'sorry')])

    def test_interpolation_expressions_are_code(self):
        for source in ['def value := s!"{by sorry}"',
                       'def value := m! "{by admit}"',
                       'def value := s! /- spacing -/ "{by native_decide}"',
                       'def value := s!"{s!"{by bv_decide}"}"',
                       'def value := s!"{(show {n : Nat // True} from ⟨0, by sorry⟩)}"',
                       'def value := s!r#"{by ofReduceBool}"#']:
            with self.subTest(source=source):
                self.assertTrue(self.violations(source))
        for source in ['def value := s!"admit {{sorry}} {"axiom"}"',
                       'def value := "{by sorry}"',
                       'def value := s!"{(\'{\', \'}\')}"']:
            with self.subTest(source=source):
                self.assertEqual(self.violations(source), [])

    def test_line_numbers_and_comment_boundaries(self):
        source = '-- sorry\n/- outer\n/- admit -/\n-/\nexample := by\n  sorry'
        self.assertEqual(self.violations(source), [(6, 'sorry')])
        self.assertEqual(self.violations('/- "/-" /- nested -/ -/ by admit'), [(1, 'unterminated comment')])
        self.assertEqual(self.violations('/- outer /- inner -/ -/ by admit'), [(1, 'admit')])

    def test_unterminated_literals_fail(self):
        for source in ['/- sorry', '"sorry', 'r#"sorry', 's!"{by trivial']:
            with self.subTest(source=source):
                self.assertTrue(self.violations(source))


if __name__ == '__main__':
    unittest.main()
