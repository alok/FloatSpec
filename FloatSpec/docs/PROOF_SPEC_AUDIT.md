# Integration Proof and Specification Audit

Date: 2026-08-28

Scope: the `integration` branch reconstructed from current `main` and the
reviewed `audit_fix` tree.

## Trust status

- Active `sorry`: 0
- Active `admit`: 0
- Project axioms: 0
- Recognized semantic placeholders: 0
- Lean files: generated in `status.md` and `status.json`

The counts are generated from active Lean syntax; comments are excluded from
placeholder matching.

## Resolved merge blockers

### Correctness names

Six same-name `Unit` declarations were removed. This audit originally kept
two exact aliases, `binary_add_correct` for `Bplus_correct` and
`binary_mul_correct` for `Bmult_correct`, and four compatibility theorems,
`binary_sub_correct`, `binary_fma_correct`, `binary_div_correct` and
`binary_sqrt_correct`. All six were deleted in batch 1D of the conventions
cutover (September 2026), together with the real-rounding `Binary754`
operations they described, and their regression tests went with them.

The source-shaped contracts are exported only under the exact Coq names
`Bplus_correct`, `Bmult_correct`, `Bminus_correct`, `Bfma_correct`,
`Bdiv_correct` and `Bsqrt_correct`. They quantify over the translated source
operations and NaN handlers, and they keep the source result equations and
the finiteness, sign and overflow obligations.

The root `binary_overflow` implementation now follows Coq's rounding-mode and
sign behavior, including the largest-finite result for RTZ overflow. This
removes the concrete RTZ counterexample that exposed the old always-infinity
implementation.

### Targeted semantic rerun

The v13 source/target judge was rerun after migrating the four remaining
source-shaped arithmetic contracts. This was a four-item audit, not a
full-repository score. A first pass identified extra `Valid_exp` and
`Monotone_exp` binders in the Lean interfaces. `Valid_exp` was already
derivable; a missing Compat bridge for the unconditional Core `Monotone_exp`
instance was added, and both redundant binders were removed from all four
public theorem signatures. A fresh target index confirmed exact-name matches
and source-shaped interfaces after that repair.

| Source item | Result | Evidence/interpretation |
|---|---|---|
| `Bminus_correct` | uncertain | Exact match; no mismatch or counterexample found; explicit Coq sign match and Lean helper appear extensionally equivalent, but three executed observations were not completed |
| `Bfma_correct` | uncertain | Exact match; exported interfaces correspond; no mismatch or counterexample found; three executed observations were not recorded before verdict |
| `Bdiv_correct` | uncertain | Exact match; no binder, premise, branch, or conclusion mismatch found; three executed observations were not completed |
| `Bsqrt_correct` | uncertain | Exact match; compiler-confirmed binders and conclusion correspond with no reported difference; three executed observations were not completed |

The target compiled during judging. All four requested jobs produced valid
verdicts with no failure category and no counterexample. They remain
conservatively `uncertain`, rather than `aligned`, because the v13 acceptance
rule requires at least three recorded, compiler-verified two-sided examples.
The overall report is intentionally `INCOMPLETE`: only four jobs were requested
from the scoped 408-job plan, so its 0% conservative score is an abstention
artifact and not a repository-wide accuracy measurement.

### `canonical_bounded`

The source-facing theorem now takes a Coq-shaped positive mantissa and the
`specFloat_bounded` predicate. The former Lean-only combination of range
boundedness, explicit positivity, and explicit canonicality is no longer
published under the Coq theorem name. Nat representation users have a separate
`canonical_bounded_nat` bridge.

### Repository hygiene

Generated `.log` history from `audit_fix` is not present. Integration commits
are split into toolchain, Core, Calc, Prop, IEEE754, Pff, tests, and
documentation/CI layers. Full model transcripts and judge evidence remain
external pipeline artifacts.

## Remaining trust boundary

Compilation, proof-hole scans, and interface regressions are necessary but not
sufficient evidence of semantic equivalence. The repository-level alignment
judge must still compare each translated declaration against the pinned Coq
source. The targeted judge found no counterexample for the four migrated
contracts, but also could not satisfy its positive three-observation gate.
Full-repository judging remains required. Judge negatives require an executable
or proof-checked counterexample; unsupported cases remain uncertain.
