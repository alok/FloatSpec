# Flocq declarations without a named Lean counterpart (2026-09-22)

The Flocq Atlas lists 192 pinned Flocq declarations (of 2,716) that had no exact-name match and no `@[flocq_source]` anchor in FloatSpec `f633f081`. Each was classified by comparing Rocq 9.1 `Check @name` with Lean `#check @name` on the built snapshot. A critic re-checked every not-applicable verdict and a sample of the matches. Per-declaration results, with both compiled types, are in [unaddressed_classification.json](unaddressed_classification.json).

| Classification | Count | Meaning |
|---|---:|---|
| renamed-match | 97 | A Lean declaration states the same thing under another name (many are legacy `_spec` Hoare triples whose P → Q reading matches). Needs an anchor, or a direct theorem under the Coq name. |
| renamed-differs | 12 | A counterpart exists but the statement differs (legacy ℤ-coded comparisons in Raux, `B754_finite` taking `ℕ` with `0 < m` where Coq takes `positive`, a stronger iff, `vNum : ℕ`). |
| missing | 14 | Nothing states it: named `ZnearestE`/`rndNE`/`rndNA`, the constructor and eliminator forms (`FIX_spec`, `FLX_format_ind`, ...) of Coq's one-constructor format inductives that Lean encodes as ∃-definitions, and `FtoRradix`. |
| not-applicable | 69 | Rocq artifacts with no Lean analogue by design: 16 automatically generated SProp eliminators (`*_sind`; Lean has no SProp) and 53 section-local notations that leave no compiled constant. |

## By Flocq file

| File | match | differs | missing | n/a |
|---|---:|---:|---:|---:|
| `src/Calc/Bracket.v` | 6 | 0 | 0 | 1 |
| `src/Calc/Round.v` | 0 | 0 | 0 | 1 |
| `src/Core/Defs.v` | 2 | 0 | 0 | 0 |
| `src/Core/FIX.v` | 0 | 0 | 2 | 1 |
| `src/Core/FLT.v` | 0 | 0 | 2 | 1 |
| `src/Core/FLX.v` | 1 | 0 | 4 | 2 |
| `src/Core/FTZ.v` | 0 | 0 | 2 | 1 |
| `src/Core/Generic_fmt.v` | 8 | 0 | 1 | 0 |
| `src/Core/Raux.v` | 26 | 7 | 0 | 0 |
| `src/Core/Round_NE.v` | 1 | 0 | 2 | 1 |
| `src/Core/Ulp.v` | 3 | 0 | 0 | 2 |
| `src/Core/Zaux.v` | 13 | 0 | 0 | 4 |
| `src/IEEE754/Binary.v` | 15 | 0 | 0 | 4 |
| `src/IEEE754/BinarySingleNaN.v` | 13 | 4 | 0 | 4 |
| `src/IEEE754/Bits.v` | 0 | 0 | 0 | 2 |
| `src/Pff/Pff.v` | 8 | 1 | 1 | 1 |
| `src/Pff/Pff2Flocq.v` | 0 | 0 | 0 | 30 |
| `src/Pff/Pff2FlocqAux.v` | 1 | 0 | 0 | 0 |
| `src/Prop/Div_sqrt_error.v` | 0 | 0 | 0 | 3 |
| `src/Prop/Mult_error.v` | 0 | 0 | 0 | 2 |
| `src/Prop/Plus_error.v` | 0 | 0 | 0 | 3 |
| `src/Prop/Round_odd.v` | 0 | 0 | 0 | 5 |
| `src/Prop/Sterbenz.v` | 0 | 0 | 0 | 1 |

## Missing and differing declarations

| Flocq declaration | Class | Lean today | Port difficulty |
|---|---|---|---|
| `src/Core/FIX.v:FIX_format_ind@928` | missing | `FloatSpec.Core.FIX.FIX_format (def; elimination via Exists.elim / obtain)` | trivial |
| `src/Core/FIX.v:FIX_spec@959` | missing | `FloatSpec.Core.FIX.FIX_format (def, anchored; no named intro rule)` | trivial |
| `src/Core/FLT.v:FLT_format_ind@1026` | missing | `FloatSpec.Core.FLT.FLT_format (def; elimination via Exists.elim / obtain)` | trivial |
| `src/Core/FLT.v:FLT_spec@1057` | missing | `FloatSpec.Core.FLT.FLT_format (def, anchored; no named intro rule)` | trivial |
| `src/Core/FLX.v:FLXN_format_ind@3315` | missing | `FloatSpec.Core.FLX.FLXN_format (def; elimination via Exists.elim / obtain)` | trivial |
| `src/Core/FLX.v:FLXN_spec@3347` | missing | `FloatSpec.Core.FLX.FLXN_format (def, anchored; no named intro rule)` | trivial |
| `src/Core/FLX.v:FLX_format_ind@1055` | missing | `FloatSpec.Core.FLX.FLX_format (def; elimination via Exists.elim / obtain)` | trivial |
| `src/Core/FLX.v:FLX_spec@1086` | missing | `FloatSpec.Core.FLX.FLX_format (def, anchored; no named intro rule)` | trivial |
| `src/Core/FTZ.v:FTZ_format_ind@1010` | missing | `FloatSpec.Core.FTZ.FTZ_format (def; elimination via Exists.elim / obtain)` | trivial |
| `src/Core/FTZ.v:FTZ_spec@1041` | missing | `FloatSpec.Core.FTZ.FTZ_format (def, anchored; no named intro rule)` | trivial |
| `src/Core/Generic_fmt.v:rndNA@54777` | missing | — | trivial |
| `src/Core/Raux.v:Rabs_eq_R0@1485` | renamed-differs | `FloatSpec.Core.Raux.Rabs_eq_R0_spec` | trivial |
| `src/Core/Raux.v:Rcompare_Eq_@7072` | renamed-differs | `FloatSpec.Core.Raux.Rcompare_prop.Rcompare_Eq_` | easy |
| `src/Core/Raux.v:Rcompare_Gt_@7121` | renamed-differs | `FloatSpec.Core.Raux.Rcompare_prop.Rcompare_Gt_` | easy |
| `src/Core/Raux.v:Rcompare_Lt_@7019` | renamed-differs | `FloatSpec.Core.Raux.Rcompare_prop.Rcompare_Lt_` | easy |
| `src/Core/Raux.v:Rcompare_Lt_inv@7603` | renamed-differs | `FloatSpec.Core.Raux.Rcompare_Lt_inv_spec` | trivial |
| `src/Core/Raux.v:Rmin_compare@11841` | renamed-differs | `FloatSpec.Core.Raux.Rmin_compare_spec` | trivial |
| `src/Core/Raux.v:eqb_false@45583` | renamed-differs | `FloatSpec.Core.Raux.eqb_false_spec` | trivial |
| `src/Core/Round_NE.v:ZnearestE@874` | missing | — | trivial |
| `src/Core/Round_NE.v:rndNE@14363` | missing | — | trivial |
| `src/IEEE754/BinarySingleNaN.v:B754_finite@2019` | renamed-differs | `BinarySingleNaNFloat.B754_finite` | hard |
| `src/IEEE754/BinarySingleNaN.v:binary_float_ind@1917` | renamed-differs | `BinarySingleNaNFloat.rec` | hard |
| `src/IEEE754/BinarySingleNaN.v:binary_float_rec@1917` | renamed-differs | `BinarySingleNaNFloat.rec` | hard |
| `src/IEEE754/BinarySingleNaN.v:binary_float_rect@1917` | renamed-differs | `BinarySingleNaNFloat.rec` | hard |
| `src/Pff/Pff.v:FtoRradix@931258` | missing | — | trivial |
| `src/Pff/Pff.v:vNum@53182` | renamed-differs | `FloatSpec.Pff.Source.Fbound.vNum` | trivial |

## Plan

1. After the Hoare-triple retirement merges, give each renamed match its Coq name as a direct theorem with a `@[flocq_source]` anchor, delete the `_spec` wrapper where nothing else calls it, and re-run the anchor statement audit.
2. Replace the legacy ℤ encoding of comparisons in Raux with `Ordering`, matching Flocq's `comparison` (hard cutover, callers rewritten).
3. Add the missing named definitions and the format constructor and eliminator lemmas, each anchored and checked against Rocq.
4. Decide `B754_finite`'s mantissa type: keep `ℕ` with `0 < m` and add an anchored `positive`-style view, or move to a `PNat` mantissa; either way, state the Coq-shaped constructor and eliminators.
5. Teach the Atlas the not-applicable class so these 69 stop counting as unaddressed.
