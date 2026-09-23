# Anchor statement audit (2026-09-22)

Every `@[flocq_source]` anchor was compared statement-for-statement with the
declaration it names in pinned Flocq `7aab8f55` under Rocq 9.1. Per-anchor
verdicts are in [anchor_statement_audit.json](anchor_statement_audit.json).

## Method

1. `scripts/ExportFlocqSources.lean` listed the 456 anchors (no duplicates).
2. For each anchor, the Lean side printed `#check @X` with `pp.proofs false`,
   and the Rocq side printed `Check @X`, `About X` (plus `Print` for
   definitions). Both were compiled against the real exports, so section
   variables that Coq drops and instance arguments that Lean auto-binds show
   up as they are, not as the source text suggests.
3. One judge per Flocq file classified each pair as `match`, `triple-shaped`
   (a legacy `Id` Hoare triple whose P → Q reading is the Rocq statement), or
   `real-mismatch`. Definitions were compared body-for-body as well.
4. Three independent refuters tried to explain away each claimed mismatch,
   and a mismatch stood only if none of them could.

## Results

| Verdict | Anchors |
|---|---:|
| match | 438 |
| triple-shaped (P → Q matches; migrated with the Hoare retirement) | 16 |
| real mismatch | 2 |

Neither real mismatch was a wrong theorem. Each was an anchor attached to the
wrong Lean declaration:

- **`round_0`**: the anchor sat on `FloatSpec.Calc.Round.round_0`, which is
  stated over the Lean-only `Mode` bundle (it assumes only `rnd 0 = 0`). That
  is a strict generalization of Flocq's `Valid_rnd` statement, not the same
  proposition. It is now `@[flocq_local]`. `FloatSpec.Core.Generic_fmt.round_0`
  was already anchored and matches exactly.
- **`SF2B'`**: the anchor sat on the raw root `SF2B'`, which returns the
  unindexed `B754` and carries no boundedness invariant. The anchor now sits
  on `BinarySingleNaN.SF2B' : StandardFloat → BinarySingleNaNFloat prec emax`,
  which matches Rocq's `spec_float → binary_float prec emax`. The raw view is
  `@[flocq_local]`.

After the fix there were 455 anchors (the `Calc` duplicate is gone). The
structural Pff transcription then anchored `Pdiv_correct`, checked the same
way (match), for 456. `scripts/validate_flocq_source_refs.py` validates all of
them against fresh compiled metadata.

## What this does and does not establish

These are model judgments over compiled statements, backed by adversarial
refutation. They do not replace the manual source-review queue
([source_review_queue.json](source_review_queue.json)), whose entries pin
compiled hashes and reopen on drift. They are the input that says where
manual review should look first. The two confirmed mismatches were both
anchor-placement errors that `validate_flocq_source_refs.py` could not see,
because it checks names and lines, not propositions.

## Later rows

Anchors added since this audit get a row, checked the same way, when they
land. The JSON header gives the base of the full audit (`full_audit_base`),
the commit its latest rows were checked on (`updated_on`), and the number of
live anchors (`anchors`), each of which has exactly one row. The two rows
listed in `superseded_rows` are the mismatches above; each keeps its
`resolution` and names a Lean declaration that no longer carries the anchor.

The batch 1D review (conventions cutover) added rows for the 12 `Binary.v` and
`BinarySingleNaN.v` operations it anchored, moved the `valid_binary` row to
`Binary.valid_binary`, and filled in the four anchors that had no row:
`BinarySingleNaN.SF2B'`, `BinarySingleNaN.shl_align_fexp`, `choice_mode` and
`FaithfulPrimFloat.B2Prim`. All of them are `match`. `Binary.Bfma_szero` is a
`match` only after its body was corrected: it had read NaN signs with `Bsign`,
where Coq reads them through `B2BSN`.

Batch 1C added 23 `match` rows: 19 `Raux.v` theorems (four of them,
`Rabs_eq_R0`, `Rinv_lt`, `Rinv_le` and `Rsqr_le_abs_0_alt`, restated to Coq's
form first), `Zrnd_opp`, and the `Double_rounding.v` definitions
`round_round_eq`, `midp` and `midp'`.

Batch 1E added 43 `Zaux.v` rows, all `match`: the 28
`Zeq_bool`/`Zle_bool`/`Zlt_bool`/`Zcompare` declarations of Zaux.v:502–764,
the four `Zsame_sign_*` lemmas, five `cond_Zopp` lemmas, `Zfast_pow_pos` and
its correctness lemma, `Zdiv_eucl_unique`, `iter_nat_plus`, `iter_nat_S` and
`iter_pos_nat`. `Zcompare_*` are now stated about Lean's `compare` on `Int`
(Rocq's `Z.compare`); the Lean-only `Zaux.Zcompare` is gone. Anchoring exposed
one statement bug: `negb_Zle_bool` and `negb_Zlt_bool` were written `!a = b`,
which Lean parses as `!(a = b)`; they now read `(!a) = b`, as in Rocq.
`Zfast_pow_pos` now follows Rocq's squaring recursion instead of computing
`v ^ n`, and `Zdiv_eucl_unique` names `Int.fmod` for `Z.modulo`. `Zeven_ex`
and `Zeven_Zpower_odd` were restated on the new `Zaux.Z.even` (Rocq's Boolean
`Z.even`) and re-checked.
