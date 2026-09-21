# Dependency-ordered Flocq review queue

Pinned source: `7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`.

Generated from actual `coqdep` dependencies and compiled `.glob` declaration offsets.
Module dependencies come first; declarations within each module follow source order.
Independent modules may be reviewed in parallel. Existing Lean names and source links
are candidates, **not reviewed contracts**. Generated recursors, constructors, notations,
and proof infrastructure are included, so totals are not a port-completion percentage.

This queue's manual review manifest starts conservatively. Historical reviewed slices
in SOURCE_CONTRACT_REVIEW.md are not automatically reclassified without precise entries.
External Rocq imports are recorded in the JSON report, not counted as Flocq declarations.

| Order | Source module | Declarations | Anchored | Name candidates | Reviewed |
|---:|---|---:|---:|---:|---:|
| 1 | src/Version.v | 1 | 1 | 1 | 1 |
| 2 | src/Core/Zaux.v | 102 | 6 | 91 | 7 |
| 3 | src/Core/Raux.v | 186 | 10 | 162 | 0 |
| 4 | src/Core/Defs.v | 14 | 11 | 14 | 0 |
| 5 | src/Core/Round_pred.v | 83 | 2 | 25 | 0 |
| 6 | src/Core/Digits.v | 67 | 0 | 67 | 0 |
| 7 | src/Core/Float_prop.v | 37 | 0 | 37 | 0 |
| 8 | src/Core/Generic_fmt.v | 145 | 33 | 140 | 0 |
| 9 | src/Calc/Operations.v | 17 | 6 | 17 | 0 |
| 10 | src/Prop/Sterbenz.v | 6 | 0 | 5 | 0 |
| 11 | src/Core/Ulp.v | 122 | 31 | 119 | 0 |
| 12 | src/Core/Round_NE.v | 21 | 7 | 17 | 0 |
| 13 | src/Core/FIX.v | 14 | 2 | 11 | 0 |
| 14 | src/Core/FLX.v | 35 | 5 | 28 | 0 |
| 15 | src/Core/FLT.v | 32 | 13 | 29 | 0 |
| 16 | src/Core/Core.v | 0 | 0 | 0 | 0 |
| 17 | src/Prop/Round_odd.v | 49 | 8 | 44 | 0 |
| 18 | src/Prop/Relative.v | 48 | 5 | 48 | 0 |
| 19 | src/Prop/Plus_error.v | 27 | 9 | 24 | 0 |
| 20 | src/Prop/Mult_error.v | 14 | 4 | 12 | 0 |
| 21 | src/Core/FTZ.v | 17 | 5 | 14 | 0 |
| 22 | src/Prop/Double_rounding.v | 108 | 0 | 108 | 0 |
| 23 | src/Prop/Div_sqrt_error.v | 27 | 6 | 24 | 0 |
| 24 | src/Pff/Pff.v | 833 | 57 | 828 | 0 |
| 25 | src/Pff/Pff2FlocqAux.v | 31 | 3 | 30 | 0 |
| 26 | src/Pff/Pff2Flocq.v | 69 | 1 | 39 | 0 |
| 27 | src/Calc/Bracket.v | 45 | 6 | 42 | 0 |
| 28 | src/Calc/Round.v | 83 | 9 | 82 | 0 |
| 29 | src/Calc/Div.v | 6 | 4 | 6 | 0 |
| 30 | src/Calc/Sqrt.v | 6 | 5 | 6 | 0 |
| 31 | src/IEEE754/BinarySingleNaN.v | 197 | 34 | 186 | 0 |
| 32 | src/IEEE754/PrimFloat.v | 46 | 0 | 46 | 0 |
| 33 | src/IEEE754/Binary.v | 167 | 22 | 156 | 0 |
| 34 | src/IEEE754/Bits.v | 56 | 24 | 54 | 0 |
| 35 | src/Calc/Plus.v | 5 | 2 | 5 | 0 |

## Next source-ordered checks

Take the first outstanding contract, inspect its imported dependencies, compare
the full Lean type/body with Rocq, and add an evidence-bearing review entry.
Resolve aliases and generated proof infrastructure explicitly; do not create
unnecessary numerical APIs to satisfy a raw name count.

- `src/Core/Zaux.v:75` — `Zeven_ex` (prf): `FloatSpec.Core.Zaux.Zeven_ex`.
- `src/Core/Zaux.v:94` — `Zpower_plus` (prf): `FloatSpec.Core.Zaux.Zpower_plus`.
- `src/Core/Zaux.v:102` — `Zpower_Zpower_nat` (prf): `FloatSpec.Core.Zaux.Zpower_Zpower_nat`.
- `src/Core/Zaux.v:113` — `Zpower_nat_S` (prf): `FloatSpec.Core.Zaux.Zpower_nat_S`.
- `src/Core/Zaux.v:123` — `Zpower_pos_gt_0` (prf): `FloatSpec.Core.Zaux.Zpower_pos_gt_0`.
- `src/Core/Zaux.v:135` — `Zeven_Zpower_odd` (prf): `FloatSpec.Core.Zaux.Zeven_Zpower_odd`.
- `src/Core/Zaux.v:147` — `radix` (rec): `FloatSpec.Core.Defs.FlocqFloat.radix`.
- `src/Core/Zaux.v:147` — `radix_val` (proj): no exact-name candidate.
- `src/Core/Zaux.v:147` — `radix_prop` (proj): no exact-name candidate.
- `src/Core/Zaux.v:149` — `radix_val_inj` (prf): `FloatSpec.Core.Zaux.radix_val_inj`.
- `src/Core/Zaux.v:161` — `radix2` (def): `FloatSpec.Core.Zaux.radix2`, `radix2`.
- `src/Core/Zaux.v:165` — `radix_gt_0` (prf): `FloatSpec.Core.Zaux.radix_gt_0`.
- `src/Core/Zaux.v:173` — `radix_gt_1` (prf): `FloatSpec.Core.Zaux.radix_gt_1`.
- `src/Core/Zaux.v:181` — `Zpower_gt_1` (prf): `FloatSpec.Core.Zaux.Zpower_gt_1`.
- `src/Core/Zaux.v:208` — `Zpower_gt_0` (prf): `FloatSpec.Core.Zaux.Zpower_gt_0`.
- `src/Core/Zaux.v:222` — `Zpower_ge_0` (prf): `FloatSpec.Core.Zaux.Zpower_ge_0`.
- `src/Core/Zaux.v:231` — `Zpower_le` (prf): `FloatSpec.Core.Zaux.Zpower_le`.
- `src/Core/Zaux.v:251` — `Zpower_lt` (prf): `FloatSpec.Core.Zaux.Zpower_lt`.
- `src/Core/Zaux.v:278` — `Zpower_lt_Zpower` (prf): `FloatSpec.Core.Zaux.Zpower_lt_Zpower`.
- `src/Core/Zaux.v:291` — `Zpower_gt_id` (prf): `FloatSpec.Core.Zaux.Zpower_gt_id`.

## Reproduce

```sh
uv run scripts/flocq_port_queue.py --flocq-dir /path/to/pinned-built-flocq \
  --coqdep /path/to/coqdep --output /tmp/flocq-queue.json \
  --markdown /tmp/SOURCE_REVIEW_QUEUE.md
```

The generator checks the source pin, tracked-source cleanliness, every `.glob` digest,
dependency precedence, source-anchor validity, manifest references, and a stable Lean
source snapshot. It rejects unsupported mutual blocks rather than inventing their order.
Manual reviews record Lean structural type/body hashes and the noncomputable flag.
These detect direct-declaration drift, not changes hidden in transitive dependencies,
and are noncryptographic change detectors, not semantic or security certificates.
CI runs `uv run scripts/flocq_port_queue.py --check-lean-reviews --skip-build`.
It does not infer semantic correspondence from matching names, compilation, or runtime tests.
