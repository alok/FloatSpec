"""Proof-carrying source clients reject optional/property-only regressions."""
import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core

ROOT = Path(__file__).resolve().parents[1]


class LeanControls(unittest.TestCase):
    def test_former_property_only_results_do_not_fit_source_clients(self):
        source = (ROOT / "FloatSpec/Test/LpoSourceContracts.lean").read_text()
        # Keep only the three exact typed consumers, so the failure cannot come
        # from a subsequent projection proof or theorem-name dependency.
        source = source.split("/-- Erasing the carried proof")[0]
        source += "\nend FloatSpec.Test.LpoSourceContracts\n"
        wrong = source
        for old, replacement in (("LPO_min P hdec", "LPO_min_choice_spec P hdec"),
                                 ("LPO P hdec", "LPO_choice_spec P hdec"),
                                 ("LPO_Z P hdec", "LPO_Z_choice_spec P hdec")):
            self.assertEqual(wrong.count(old), 1)
            wrong = wrong.replace(old, replacement)
        with tempfile.TemporaryDirectory(prefix="floatspec-lpo-lean-control-") as directory:
            path = Path(directory) / "Control.lean"
            path.write_text(source)
            core.run(["lake", "env", "lean", str(path)])
            path.write_text(wrong)
            with self.assertRaises(RuntimeError) as failure:
                core.run(["lake", "env", "lean", str(path)])
            message = str(failure.exception)
            self.assertEqual(message.count("error: Type mismatch"), 3)
            self.assertEqual(message.count("of sort `Prop`"), 3)
            self.assertEqual(message.count("of sort `Type`"), 3)


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class RocqControls(unittest.TestCase):
    def test_erasing_witness_proof_does_not_fit_source_client(self):
        source = (ROOT / "scripts/fixtures/LpoSourceContracts.v").read_text()
        source = source.replace("Definition minClient", r"""
Definition erasedNatChoice (P : nat -> Prop) (hdec : forall n, P n \/ ~ P n) : option nat :=
  match LPO P hdec with
  | inleft witness => Some (proj1_sig witness)
  | inright _ => None
  end.

Definition minClient""", 1)
        expected = ":= LPO P hdec."
        self.assertEqual(source.count(expected), 1)
        wrong = source.replace(expected, ":= erasedNatChoice P hdec.")
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with tempfile.TemporaryDirectory(prefix="floatspec-lpo-rocq-control-") as directory:
            path = Path(directory) / "Control.v"
            command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"), "Flocq", str(path)]
            path.write_text(source)
            core.run(command)
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, 'has type "option nat"'):
                core.run(command)


if __name__ == "__main__":
    unittest.main()
