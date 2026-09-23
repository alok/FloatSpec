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
and `binary_mul_correct` aliases. Flocq's names now refer only to the
computable, proof-carrying ports in namespaces `Binary` and `BinarySingleNaN`,
whose contracts are exported as `Bplus_correct`, `Bmult_correct`,
`Bminus_correct`, `Bfma_correct`, `Bdiv_correct`, and `Bsqrt_correct`.

The shared overflow helper is mode-sensitive as in Coq: nearest modes choose
infinity, round-toward-zero chooses the largest finite value, and directed
modes choose according to the sign. The source-shaped contracts connect that
helper to the translated source operations.

## Audit interpretation

Zero placeholder findings means that active Lean syntax contains no recognized
proof hole or trivial semantic replacement. It does not prove cross-language
semantic equivalence. Source alignment remains a declaration-by-declaration
review and judge obligation.
