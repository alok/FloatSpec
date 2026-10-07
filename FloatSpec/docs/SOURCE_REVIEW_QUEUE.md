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
| 2 | src/Core/Zaux.v | 102 | 82 | 91 | 102 |
| 3 | src/Core/Raux.v | 186 | 168 | 178 | 186 |
| 4 | src/Core/Defs.v | 14 | 11 | 14 | 14 |
| 5 | src/Core/Round_pred.v | 83 | 78 | 78 | 83 |
| 6 | src/Core/Digits.v | 67 | 63 | 67 | 63 |
| 7 | src/Core/Float_prop.v | 37 | 36 | 37 | 37 |
| 8 | src/Core/Generic_fmt.v | 145 | 35 | 140 | 0 |
| 9 | src/Calc/Operations.v | 17 | 7 | 17 | 0 |
| 10 | src/Prop/Sterbenz.v | 6 | 0 | 5 | 0 |
| 11 | src/Core/Ulp.v | 122 | 31 | 119 | 0 |
| 12 | src/Core/Round_NE.v | 21 | 10 | 17 | 3 |
| 13 | src/Core/FIX.v | 14 | 2 | 11 | 0 |
| 14 | src/Core/FLX.v | 35 | 5 | 28 | 0 |
| 15 | src/Core/FLT.v | 32 | 13 | 29 | 0 |
| 16 | src/Core/Core.v | 0 | 0 | 0 | 0 |
| 17 | src/Prop/Round_odd.v | 49 | 8 | 44 | 0 |
| 18 | src/Prop/Relative.v | 48 | 5 | 48 | 0 |
| 19 | src/Prop/Plus_error.v | 27 | 9 | 24 | 0 |
| 20 | src/Prop/Mult_error.v | 14 | 4 | 12 | 0 |
| 21 | src/Core/FTZ.v | 17 | 5 | 14 | 0 |
| 22 | src/Prop/Double_rounding.v | 108 | 3 | 108 | 0 |
| 23 | src/Prop/Div_sqrt_error.v | 27 | 6 | 24 | 0 |
| 24 | src/Pff/Pff.v | 833 | 58 | 828 | 0 |
| 25 | src/Pff/Pff2FlocqAux.v | 31 | 3 | 30 | 0 |
| 26 | src/Pff/Pff2Flocq.v | 69 | 1 | 39 | 0 |
| 27 | src/Calc/Bracket.v | 45 | 6 | 42 | 0 |
| 28 | src/Calc/Round.v | 83 | 9 | 82 | 0 |
| 29 | src/Calc/Div.v | 6 | 4 | 6 | 0 |
| 30 | src/Calc/Sqrt.v | 6 | 5 | 6 | 0 |
| 31 | src/IEEE754/BinarySingleNaN.v | 197 | 41 | 186 | 0 |
| 32 | src/IEEE754/PrimFloat.v | 46 | 1 | 46 | 0 |
| 33 | src/IEEE754/Binary.v | 167 | 34 | 156 | 0 |
| 34 | src/IEEE754/Bits.v | 56 | 24 | 54 | 0 |
| 35 | src/Calc/Plus.v | 5 | 2 | 5 | 0 |

## Next source-ordered checks

Take the first outstanding contract, inspect its imported dependencies, compare
the full Lean type/body with Rocq, and add an evidence-bearing review entry.
Resolve aliases and generated proof infrastructure explicitly; do not create
unnecessary numerical APIs to satisfy a raw name count.

- `src/Core/Digits.v:25` — `digits2_pos` (abbrev): `FloatSpec.Core.Digits.digits2_pos`.
- `src/Core/Digits.v:26` — `Zdigits2` (abbrev): `FloatSpec.Core.Digits.Zdigits2`.
- `src/Core/Digits.v:1153` — `Zpos_digits2_pos` (prf): `FloatSpec.Core.Digits.Zpos_digits2_pos`.
- `src/Core/Digits.v:1165` — `Zdigits2_Zdigits` (prf): `FloatSpec.Core.Digits.Zdigits2_Zdigits`.
- `src/Core/Generic_fmt.v:30` — `bpow` (abbrev): `FloatSpec.Core.Raux.Source.bpow`, `FloatSpec.Core.Raux.bpow`.
- `src/Core/Generic_fmt.v:38` — `Valid_exp` (ind+rec): `FloatSpec.Core.Generic_fmt.Valid_exp`.
- `src/Core/Generic_fmt.v:39` — `valid_exp` (constr+proj): `FloatSpec.Core.Generic_fmt.Valid_exp.valid_exp`.
- `src/Core/Generic_fmt.v:48` — `valid_exp_large` (prf): `FloatSpec.Core.Generic_fmt.valid_exp_large`.
- `src/Core/Generic_fmt.v:61` — `valid_exp_large'` (prf): `FloatSpec.Core.Generic_fmt.valid_exp_large'`.
- `src/Core/Generic_fmt.v:76` — `cexp` (def): `FloatSpec.Core.Generic_fmt.cexp`, `cexp`.
- `src/Core/Generic_fmt.v:79` — `canonical` (def): `FloatSpec.Core.Generic_fmt.canonical`.
- `src/Core/Generic_fmt.v:82` — `scaled_mantissa` (def): `FloatSpec.Core.Generic_fmt.scaled_mantissa`.
- `src/Core/Generic_fmt.v:85` — `generic_format` (def): `FloatSpec.Core.Generic_fmt.generic_format`, `generic_format`.
- `src/Core/Generic_fmt.v:89` — `generic_format_0` (prf): `FloatSpec.Core.Generic_fmt.generic_format_0`.
- `src/Core/Generic_fmt.v:97` — `cexp_opp` (prf): `FloatSpec.Core.Generic_fmt.cexp_opp`.
- `src/Core/Generic_fmt.v:106` — `cexp_abs` (prf): `FloatSpec.Core.Generic_fmt.cexp_abs`.
- `src/Core/Generic_fmt.v:115` — `canonical_generic_format` (prf): `FloatSpec.Core.Generic_fmt.canonical_generic_format`.
- `src/Core/Generic_fmt.v:129` — `generic_format_bpow` (prf): `FloatSpec.Core.Generic_fmt.generic_format_bpow`.
- `src/Core/Generic_fmt.v:145` — `generic_format_bpow'` (prf): `FloatSpec.Core.Generic_fmt.generic_format_bpow'`.
- `src/Core/Generic_fmt.v:159` — `generic_format_F2R` (prf): `FloatSpec.Core.Generic_fmt.generic_format_F2R`.

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
