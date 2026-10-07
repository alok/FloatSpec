import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import flocq_bridge as bridge
import digits_bridge as digits


class DigitsTests(unittest.TestCase):
    def test_domains_and_repeatable_boundaries(self):
        cases = digits.corpus(865701, 20)
        self.assertEqual(cases, digits.corpus(865701, 20))
        self.assertNotEqual(cases, digits.corpus(865702, 20))
        self.assertEqual(len(cases), len(set(cases)))
        for b in digits.RADICES:
            for n in (b**32 - 1, b**32, -(b**32), b**64 + 1):
                self.assertIn(digits.Case('digits', (b, n)), cases)
            self.assertIn(digits.Case('digit', (b, -1000, -1)), cases)
            self.assertIn(digits.Case('slice', (b, -1000, 1, -1)), cases)
        for p in (1, 2**52, 2**53 - 1, 2**64):
            self.assertIn(digits.Case('binary_length', (p,)), cases)
        for op, args in [('digit', (1, 5, 0)), ('digit', (0, 5, 0)), ('digits', (10,)),
                         ('binary_length', (0,)), ('binary_length', (-3,)),
                         ('sum_digit', (10, 5, -1)), ('scale', (10, 5, 1.0)),
                         ('slice', (10, 5, 'sorry', 1))]:
            with self.subTest(op=op, args=args), self.assertRaises(ValueError):
                digits.Case(op, args)

    def test_truncating_oracle(self):
        # Z.quot/Z.rem truncate toward zero; Python's // and % floor.
        for (a, b), (q, r) in {(7, 2): (3, 1), (-7, 2): (-3, -1), (7, -2): (-3, 1),
                               (-7, -2): (3, -1), (7, 0): (0, 7)}.items():
            self.assertEqual((digits.quot(a, b), digits.rem(a, b)), (q, r))
        expect = lambda op, *args: digits.expected(digits.Case(op, args))
        self.assertEqual(expect('digit', 10, -4321, 1), [-2])
        self.assertEqual(expect('digit', 10, 4321, -1), [0])
        self.assertEqual(expect('scale', 10, -4321, -2), [-43])
        self.assertEqual(expect('scale', 10, 43, 2), [4300])
        self.assertEqual(expect('slice', 10, -654321, 2, 3), [-543])
        self.assertEqual(expect('slice', 10, 654321, -1, 3), [210])
        self.assertEqual(expect('slice', 10, 654321, 1, -1), [0])
        self.assertEqual(expect('sum_digit', 10, -654321, 3), [-321])
        self.assertEqual(expect('digits', 10, -1000), [4])
        self.assertEqual(expect('digits', 10, 999), [3])
        self.assertEqual(expect('digits', 2, 0), [0])
        self.assertEqual(expect('binary_length', 8), [3])
        lean, rocq = digits.expressions(digits.Case('binary_length', (5,)))
        self.assertIn('Zaux.Positive.xI (Zaux.Positive.xO Zaux.Positive.xH)', lean)
        self.assertIn('(5)%positive', rocq)
        lean, rocq = digits.expressions(digits.Case('sum_digit', (10, -12, 3)))
        self.assertEqual(lean, '[Digits.Zsum_digit 10 (Digits.Zdigit 10 (-12)) 3]')
        self.assertIn('Zsum_digit (Build_radix 10 eq_refl) (Zdigit (Build_radix 10 eq_refl) (-12)) 3',
                      rocq)

    def test_profile_restores_globals_and_rejects_shared_wrong_answers(self):
        original = bridge.Case
        case = digits.Case('digit', (10, -4321, 1))
        with digits.profile() as metadata:
            self.assertEqual(bridge.compare([case], {p: [[-2]] for p in ('lean', 'compiled', 'rocq')}), [])
            self.assertEqual(metadata['oracle_assertions'], 1)
            with self.assertRaises(AssertionError):
                bridge.compare([case], {p: [[8]] for p in ('lean', 'compiled', 'rocq')})
        self.assertIs(bridge.Case, original)

    @unittest.skipUnless(os.environ.get('FLOCQ_AUDIT_DIR'), 'requires pinned built Rocq')
    def test_live_oracle_detects_both_sides_mutated(self):
        reference = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        # One (before, after) edit per prover: (Lean, Rocq).
        for case, edits in [
            (digits.Case('digit', (10, -4321, 1)), [('Zdigit', 'Zscale')] * 2),
            (digits.Case('scale', (10, -4321, -2)), [('(-2)', '(2)')] * 2),
            (digits.Case('slice', (10, -654321, 2, 3)), [('(3)]', '(4)]')] * 2),
            (digits.Case('digits', (10, -1000)), [('(-1000)', '(-999)')] * 2),
            (digits.Case('binary_length', (8,)),
             [(' : Int)]', ' + 1 : Int)]'), (')]', ') + 1]')])]:
            with self.subTest(case=case), tempfile.TemporaryDirectory() as tmp, digits.profile():
                folder = Path(tmp)
                rows = bridge.execute([case], reference, bridge.configured_coqc(reference), folder)
                self.assertEqual(bridge.compare([case], rows), [])
                bridge.bootstrap_lean([case], rows['rocq'], folder)
                original = bridge.expressions
                def mutated(value):
                    pair = original(value)
                    self.assertTrue(all(text.count(before) == 1
                                        for text, (before, _) in zip(pair, edits, strict=True)))
                    return tuple(text.replace(before, after)
                                 for text, (before, after) in zip(pair, edits, strict=True))
                with patch.object(bridge, 'expressions', mutated):
                    wrong = bridge.execute([case], reference, bridge.configured_coqc(reference), folder)
                    self.assertEqual(wrong['rocq'], wrong['lean'])
                    self.assertEqual(wrong['rocq'], wrong['compiled'])
                    with self.assertRaisesRegex(AssertionError, 'independent oracle'):
                        bridge.compare([case], wrong)


if __name__ == '__main__':
    unittest.main()
