# Source Alignment Boundaries

This document records intentional compatibility boundaries that must not be
mistaken for Flocq source declarations.

## Boundedness representations

Flocq's `SpecFloat.bounded prec emax m e` combines canonical mantissa evidence
with the upper exponent bound. FloatSpec exposes this source shape as
`specFloat_bounded`.

The older Lean `bounded` predicate additionally models range checks used by
legacy Nat-based carriers. It is a compatibility predicate, not the Coq
notation. Source-facing finite constructors and `canonical_bounded` use
`specFloat_bounded`; Nat callers use the explicitly named
`canonical_bounded_nat` bridge.

## The deleted real-rounding `Binary754` layer

The permissive `Binary754` carrier used to carry its own arithmetic: `Bplus`,
`Bminus`, `Bmult`, `Bfma`, `Bdiv`, `Bsqrt`, `Bnearbyint`, `Bfrexp`, `Bsucc`,
`Bpred`, `Btrunc`, `Bulp`, `Bcompare` and the `binary_*` helpers, together with
a `BinarySingleNaNBridge` namespace. These rounded the exact real result in ℝ
and rebuilt a float from it, so they never overflowed, and all of them were
noncomputable. They have been deleted, together with the `binary_add_correct`
and `binary_mul_correct` aliases. No root-level declaration named `Bplus`,
`Bminus`, `Bmult`, `Bfma`, `Bfma_szero`, `Bdiv`, `Bsqrt`, `Bnearbyint`,
`Bfrexp`, `Bsucc`, `Bpred`, `Btrunc`, `Bulp`, `Bmax_float`,
`Bnormfr_mantissa` or `Bcompare` remains. Each of these Flocq names is
anchored with `@[flocq_source]` on the computable, proof-carrying port in
namespace `Binary` (for `Binary.v`) and in namespace `BinarySingleNaN` (for
`BinarySingleNaN.v`). Their contracts are exported as `Bplus_correct`,
`Bmult_correct`, `Bminus_correct`, `Bfma_correct`, `Bdiv_correct` and
`Bsqrt_correct`.

`Binary.v` defines `Bplus`, `Bminus`, `Bmult`, `Bfma`, `Bdiv` and `Bsqrt` as
the `BinarySingleNaN` operation on the `B2BSN` images, lifted back with
`BSN2B`. The Lean `Binary` versions are direct case splits, and
`FloatSpec/Test/SourceSurface.lean` proves each equal to that composition on
every input. `Binary.Bfma_szero` used to read NaN signs with `Bsign`. Coq reads
them through `B2BSN`, which forgets them, so the two disagreed on NaN operands.
It now reads them through `B2BSN` as Coq does. `Binary.Bfma` only calls it on
non-NaN operands, so no arithmetic result changed.

The shared overflow helper is mode-sensitive as in Coq: nearest modes choose
infinity, round-toward-zero chooses the largest finite value, and directed
modes choose according to the sign. The source-shaped contracts connect that
helper to the translated source operations.

## Flocq names that still have more than one Lean declaration

Batch 1D removed the real-rounding homonyms, but these Flocq-named Lean
declarations remain alongside the anchored ports. Each is scheduled in a later
batch of `CONVENTIONS_CUTOVER_PLAN.md`.

- `ExperimentalSingleNaNArithmetic.{Bplus, Bminus, Bulp, Bulp', Bsucc, Bsucc',
  Bpred, Bpred_pos', Bldexp, Bmax_float}` compute on the raw `B754` carrier and
  carry no anchors. They go in the 5A dedup.
- `FaithfulPrimFloat` has its own copies of about 26 operations, among them
  `Bplus`, `Bminus`, `Bmult`, `Bdiv`, `Bsqrt`, `Bfrexp`, `Bulp'`, `Bsucc`,
  `Bpred`, `Bcompare`, `Bldexp`, `binary_round_aux`, `binary_round`,
  `binary_normalize`, `Bone`, `Bsign`, `is_nan` and `is_finite`. They are
  deleted in a 5A sub-step, which restates the `*_equiv` theorems against
  `BinarySingleNaN.*`.
- `FloatSpec.IEEE754.BinarySingleNaN.Source.{Bmult, Bplus, Bminus, Bfma, Bdiv,
  Bsqrt}` take the source `mode` and delegate to `BinarySingleNaN.*`. They are
  anchored to the same Coq lines as `BinarySingleNaN.*`, and they go when 4F
  replaces the facade `mode` with `RoundingMode`.
- `Source.mode` and `Source.round_mode` hold the `mode` and `round_mode`
  anchors until 4F creates `BinarySingleNaN.mode` and
  `BinarySingleNaN.round_mode`, which must take the anchors over.
- The root `valid_binary`, on the Nat-payload `FullFloat`, is unanchored; the
  `Binary.v` anchor is on `Binary.valid_binary`, over `full_float`. The root
  `binary_round_aux`, `binary_round`, `binary_normalize`, `binary_overflow`,
  `B2R`, `Bsign`, `B2BSN`, `BSN2B`, `Bone` and `is_nan` also compute on the
  compatibility carriers. All of them go with the `Binary754` carrier in 5A.
- `BinarySingleNaNFloat.Bnormfr_mantissa` is the implementation behind the
  anchored `BinarySingleNaN.Bnormfr_mantissa` abbrev. `Binary.binary_overflow`
  is unanchored beside the anchored `Binary.binary_overflow_exact`. Both are
  for the 6D anchor sweep.

## Audit interpretation

Zero placeholder findings means that active Lean syntax contains no recognized
proof hole or trivial semantic replacement. It does not prove cross-language
semantic equivalence. Source alignment remains a declaration-by-declaration
review and judge obligation.
