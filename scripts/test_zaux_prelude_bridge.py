import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import flocq_bridge as bridge
import zaux_prelude_bridge as prelude


class PreludeTests(unittest.TestCase):
    def test_domains_and_repeatable_binary_boundaries(self):
        cases = prelude.corpus(864211, 20)
        self.assertEqual(cases, prelude.corpus(864211, 20))
        self.assertNotEqual(cases, prelude.corpus(864212, 20))
        self.assertEqual(len(cases), len(set(cases)))
        for n in (1, 2, 3, 31, 32, 33, 127, 128, 129, 257):
            self.assertIn(prelude.Case('positive_iteration', (n, 2, 3, -5)), cases)
        for op, args in [('positive_iteration', (0, 1, 1, 1)),
                         ('positive_iteration', (-1, 1, 1, 1)),
                         ('conditional_negation', (2, 1)),
                         ('conditional_negation', (True, 1)),
                         ('positive_iteration', (1, 'sorry', 1, 1))]:
            with self.subTest(op=op, args=args), self.assertRaises(ValueError):
                prelude.Case(op, args)

    def test_closed_oracle_and_no_silent_source_coercion(self):
        for n in range(1, 20):
            for a in range(-3, 4):
                x, b, initial = -2, 3, -2
                for _ in range(n):
                    x = a*x+b
                self.assertEqual(prelude.expected(prelude.Case('positive_iteration',
                                                             (n, a, b, initial))), [x])
        lean, rocq = prelude.expressions(prelude.Case('positive_iteration', (5, 2, 3, -2)))
        self.assertIn('Positive.xI (Positive.xO Positive.xH)', lean)
        self.assertIn('(5)%positive', rocq)

    def test_profile_restores_globals_and_rejects_shared_wrong_answers(self):
        original = bridge.Case
        case = prelude.Case('positive_iteration', (3, 2, 3, -2))
        with prelude.profile() as metadata:
            self.assertEqual(bridge.compare([case], {p: [[5]] for p in ('lean', 'compiled', 'rocq')}), [])
            self.assertEqual(metadata['oracle_assertions'], 1)
            with self.assertRaises(AssertionError):
                bridge.compare([case], {p: [[6]] for p in ('lean', 'compiled', 'rocq')})
        self.assertIs(bridge.Case, original)

    @unittest.skipUnless(os.environ.get('FLOCQ_AUDIT_DIR'), 'requires pinned built Rocq')
    def test_live_oracle_detects_both_sides_mutated(self):
        reference = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        for case, before, after in [
            (prelude.Case('positive_iteration', (3, 2, 3, -2)), ' + (3)', ' - (3)'),
            (prelude.Case('conditional_negation', (1, -7)), 'cond_Zopp true', 'cond_Zopp false')]:
            with self.subTest(case=case), tempfile.TemporaryDirectory() as tmp, prelude.profile():
                folder = Path(tmp)
                rows = bridge.execute([case], reference, bridge.configured_coqc(reference), folder)
                self.assertEqual(bridge.compare([case], rows), [])
                bridge.bootstrap_lean([case], rows['rocq'], folder)
                original = bridge.expressions
                def mutated(value):
                    pair = original(value)
                    self.assertTrue(all(text.count(before) == 1 for text in pair))
                    return tuple(text.replace(before, after) for text in pair)
                with patch.object(bridge, 'expressions', mutated):
                    wrong = bridge.execute([case], reference, bridge.configured_coqc(reference), folder)
                    self.assertEqual(wrong['rocq'], wrong['lean'])
                    self.assertEqual(wrong['rocq'], wrong['compiled'])
                    with self.assertRaisesRegex(AssertionError, 'independent oracle'):
                        bridge.compare([case], wrong)


if __name__ == '__main__':
    unittest.main()
