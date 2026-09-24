# FloatSpec

Formally verified floating‑point library for Lean 4, ported from the Coq Flocq project. FloatSpec aims to provide a clear, modular formalization of IEEE 754 style arithmetic together with executable reference functions and machine‑checked specifications/proofs.


## Using FloatSpec with Lean's `Float`

Lean core defines `Float` (binary64) and `Float32` (binary32) arithmetic
through a logical model: `x + y` is `Float.ofModel (x.toModel + y.toModel)`.
`FloatSpec.IEEE754.NativeFloat` proves that `+`, `-`, `*`, `/` and
`Float.sqrt` on these types are correctly rounded over the reals.

```lean
import FloatSpec.src.IEEE754.NativeFloat

open FloatSpec.IEEE754.NativeFloat
open FloatSpec.IEEE754.BinarySingleNaN.Source (mode round_mode)

-- Output abbreviated: `roundR` is `FloatSpec.Core.Generic_fmt.roundR`.
#check @add_eq_round
-- ∀ (x y : Float), x.isFinite = true → y.isFinite = true →
--   |roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE) (toReal x + toReal y)| < 2 ^ 1024 →
--   toReal (x + y) = roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE) (toReal x + toReal y) ∧
--   (x + y).isFinite = true

#check @add_standard_model
-- (same hypotheses) →
--   ∃ ε η, |ε| ≤ 2 ^ (-53) ∧ |η| ≤ 2 ^ (-1075) ∧ ε * η = 0 ∧
--     toReal (x + y) = (toReal x + toReal y) * (1 + ε) + η
```

What is proved:

- `toReal x` is Flocq's `B2R (toBinary x)`, where `toBinary` decodes
  `x.toModel` into Flocq's binary64 type. `toBinary` is a bijection
  (`binaryEquiv`). Infinities and NaN have `toReal = 0`, as in Flocq.
- `add_correct`, `sub_correct`, `mul_correct`, `div_correct` and `sqrt_correct`
  restate Flocq's `Bplus_correct`, `Bminus_correct`, `Bmult_correct`,
  `Bdiv_correct` and `Bsqrt_correct` for the native operators. The premises are
  Flocq's: finite operands for `+` and `-`, `toReal y ≠ 0` for `/`, none for
  `*` and `sqrt`. So are the conclusions: the rounded value, finiteness and sign
  when the rounded result is below `2 ^ 1024` in magnitude, and the overflow
  result otherwise (a square root cannot overflow).
- `add_eq_round`, `sub_eq_round`, `mul_eq_round` and `div_eq_round` state the
  no-overflow case with a plain inequality; `sqrt_eq_round` needs no
  hypothesis. `round_abs_lt_of_abs_le` discharges the inequality when the
  exact result is at most `(2 ^ 53 - 1) * 2 ^ 971`, the largest finite binary64
  value, in magnitude.
- `add_standard_model` through `sqrt_standard_model` give the standard model
  with underflow, from Flocq's `error_N_FLT`, under the same hypotheses.
- `FloatSpec.IEEE754.NativeFloat32` has the same theorems for `Float32`, with
  precision 24, exponent function `FLT_exp (-149) 24`, overflow bound
  `2 ^ 128`, `|ε| ≤ 2 ^ (-24)` and `|η| ≤ 2 ^ (-150)`.
- The theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
  `FloatSpec/Test/NativeFloat.lean` prints their statements and axioms, and
  checks concrete values in the kernel, for example that `0.1 + 0.2` is the
  correctly rounded sum of the binary64 values of `0.1` and `0.2`.

What is not proved:

- The theorems are about Lean's logical model. Compiled code calls the C
  operators instead (`lean_float_add`, `sqrt` and so on). That these agree with
  the model is part of what Lean trusts about its compiler and runtime.
- Only `+`, `-`, `*`, `/` and `sqrt` are covered. Lean 4.34 has no fused
  multiply-add on `Float`. The transcendental functions, `pow`, `cbrt`, `ceil`,
  `floor`, `round`, `frExp`, `scaleB` and `toString` are opaque to the kernel,
  so nothing follows from their definitions. Conversions, comparisons,
  negation and `abs` have models, and `LeanFloat.lean` relates some of them to
  Flocq, but `NativeFloat` states no real-valued theorem about them.
- A real-valued conclusion says little about a non-finite result, since
  `toReal` is `0` there; the finiteness conjuncts carry that information.
- Rounding is always to nearest, ties to even. Lean's `Float` has no other
  rounding modes.

FloatSpec is Hantao Lou's Lean port of Flocq, and the bridge from
`Float.Model` to Flocq (`FloatSpec/src/IEEE754/LeanFloat.lean` and the
`FloatSpec.IEEE754.Native` adapters) is his work. `NativeFloat` composes that
bridge with the ported Flocq theorems. It follows the Lean FRO's suggestion
that float libraries prove equivalence with `Float.Model` and transfer their
lemmas to `Float` ([Julia Markus Himmel, "Float Q&A", 2026-06-19](https://juliahimmel.de/blog/float-qanda)).


## Purpose

- Provide a Lean 4 formalization of floating‑point arithmetic that mirrors the structure and guarantees of Flocq (by Boldo & Melquiond), while integrating with Lean 4 tooling and Mathlib.
- Offer executable reference operations and source-facing mathematical
  specifications stated as direct propositions.
- Serve as a foundation for reasoning about rounding, ulp, error bounds, and IEEE 754 encodings/decodings in Lean 4.


## Architecture

The library is organized into layered modules. The top‑level aggregator `FloatSpec.lean` re‑exports the submodules for convenience.

- Core (`FloatSpec/src/Core`)
  - Basic definitions and helpers: `Defs.lean`, `Zaux.lean`, `Raux.lean`, `Digits.lean`
  - Generic formats and rounding: `Generic_fmt.lean`, `Round_pred.lean`, `Round_NE.lean`, `Ulp.lean`, `FIX.lean`, `FLX.lean`, `FLT.lean`, `FTZ.lean`
- Calc (`FloatSpec/src/Calc`)
  - Executable reference operations with specifications: `Operations.lean` (align, plus, neg, abs, mult), `Sqrt.lean`, `Div.lean`, `Plus.lean`, `Round.lean`, and bracketing utilities `Bracket.lean`
- Prop (`FloatSpec/src/Prop`)
  - Error bounds and classical theorems about rounding: `Plus_error.lean`, `Div_sqrt_error.lean`, `Double_rounding.lean`, `Relative.lean`, `Round_odd.lean`, `Sterbenz.lean`
- ErrorBound (`FloatSpec/src/ErrorBound`)
  - Reserved VCFloat-style integration modules: `Types.lean`, `RExpr.lean`, `MakeRounding.lean`, `Absolute.lean`, `Compose.lean`, `Examples/FPBench.lean`; these files are currently empty and expose no error-bound API
- IEEE754 (`FloatSpec/src/IEEE754`)
  - Encodings/decodings, bit‑level operations, and a structured IEEE 754 view: `Binary.lean`, `BinarySingleNaN.lean`, `Bits.lean`, and a bridge to primitive floats `PrimFloat.lean`
- Compat (`FloatSpec/src/Compat.lean`)
  - Thin compatibility bridges exposing selected core functions under simpler names/signatures
- Pff (`FloatSpec/src/Pff`)
  - Legacy compatibility modules and conversion helpers from an older floating‑point formalization

Project configuration lives in `lakefile.lean` and `lean-toolchain` (Lean 4
`v4.34.0`). Mathlib and CSLib remain pinned to their `v4.34.0-rc2` source
revisions; this combination builds on macOS with stable 4.34.0.


## Current Progress

The project is actively under development. No named `sorry` obligations
remain, and `FloatSpec/docs/proof_debts.json` is empty. The raw-bit sign flip
and the native next-up/next-down operations are proved equal to Flocq's `Bopp`,
`Bsucc` and `Bpred` over every binary64 bit pattern. The native `frExp`
correspondence is proved for a bit-level `nativeFrExp`; its agreement with
Lean's opaque runtime `Float.frExp` is checked by execution, not by the kernel.
A successful build checks every proof against its statement; it does not by
itself establish whole-library equivalence to Flocq. Source-facing APIs and compatibility helpers remain
distinct.

- Build: the checked-in toolchain is stable Lean 4 `v4.34.0`. The rc2 Lake
  executable crashed on this macOS host; plain `lake build` now works here.
- Proof framework: no source proof invokes `mvcgen` or `mspec`. Their unused
  `@[spec]` annotations, tactic imports, and Hoare-style linter were removed.
  Every theorem now states a direct proposition; the legacy `Id` Hoare
  triples are retired. `scripts/test_unused_mvcgen.sh` keeps them out, allowing
  `Std.Do` only in `SimprocWP.lean`, `Core/Zaux.lean` and `Calc/Sqrt.lean`.
- Trust gates: `scripts/audit_placeholders.sh` and
  `scripts/check_proof_debts.py` reject unregistered proof holes and trust
  escapes in every Lean and Rocq source outside `Deps/`, standalone fixtures
  included; `scripts/status_report.sh` records the current counts under
  `FloatSpec/docs/status.{md,json}`. CI also runs every fixture, found by
  glob, with Lean warnings as errors, and every live test module without skips,
  and `scripts/KernelReplay.lean` sends every source, test and fixture
  declaration back through the kernel, so one a metaprogram added unchecked
  fails however it was spelled.
- Source links: `@[flocq_source "src/Module.v" LINE "name"]` stores a pinned
  Coq correspondence, and the opt-in `linter.coqSource` checks public
  definitions in source-facing modules. An adjacent `Source:` URL is clickable
  in editors that recognize URLs; clicking the attribute's path string itself
  is not yet an LSP navigation feature. Coverage is incremental, not a claim
  that every public definition has been mapped.
- Start with the [linear reading guide](FloatSpec/docs/READING_GUIDE.md) for
  the distinction between module coverage, source alignment, and proof status.
- Source contracts: regression modules under `FloatSpec/Test` cover important
  representation, rounding-mode, primitive-float, Pff, and IEEE correctness-name mappings.
- ErrorBound status: `FloatSpec/src/ErrorBound.lean` is an import aggregator,
  but its six component modules are currently empty. The VCFloat-style layer
  remains planned work, not implemented support.
- VCFloat integration plan and tasks live in `FloatSpec/docs/vcfloat_integration/ARCHITECTURE_AND_PLAN.md` and `FloatSpec/docs/vcfloat_integration/TODOs.md`.
- Status artifacts:
  - Progress PDF: `FloatSpec_status.pdf`
  - Detailed Core status: `FloatSpec/src/Core/Status.md`
- Examples of completed or near‑complete components:
  - Executable alignment, negation, absolute value, addition, and multiplication with direct specifications: `FloatSpec/src/Calc/Operations.lean`
  - Executable square root core and top‑level structure theorem: `FloatSpec/src/Calc/Sqrt.lean`
  - Foundational definitions and simple structural specs: `FloatSpec/src/Core/Defs.lean`

Version: the library exposes `FloatSpec.version = "0.7.0"` (see `FloatSpec.lean`).


## Quick Start

Prerequisites

- Lean 4 toolchain: `leanprover/lean4:v4.34.0` (see `lean-toolchain`)
- Lake build tool (included with the toolchain)

Build locally

1) Build the locked dependencies and library: `lake build` (`lake update`
   would change the reviewed dependency pins and is not required).
2) Run trust gates: `scripts/audit_placeholders.sh --json FloatSpec`
   and `scripts/check_proof_debts.py`.
3) With Rocq and autotools installed, run the executable cross-language
   regressions: `scripts/test_flocq_conformance.sh`. The script checks out the
   exact `Deps/flocq` gitlink in a temporary worktree (or clone), builds it,
   and runs paired Flocq/Lean observations without modifying an existing
   nested checkout.

Lean-level tests (smoke/property checks)

- Build and run the lightweight Plausible-based tests: `lake build FloatSpecTests`
- Or use the helper script: `./scripts/test_lean.sh`

REPL and usage

- In a Lean file, import the library root or a specific area:
  - `import FloatSpec` (re‑exports) or
  - `import FloatSpec.src.Calc.Operations`
  - `import FloatSpec.src.ErrorBound` (VCFloat‑style error‑bound scaffold)
- Example (informal sketch):
  - Use `FloatSpec.Core.Defs.F2R` to interpret `FlocqFloat` as a real number
  - Use `FloatSpec.Calc.Operations.Falign`/`Fplus` to add two floats, with specs `Falign_spec`/`F2R_plus`

Use as a dependency (Lake)

If you want to depend on this repository, add a line like the following to your project’s `lakefile.lean` (pin to a commit or tag that you control):

```
require FloatSpec from git "https://github.com/Beneficial-AI-Foundation/FloatSpec" @ "<commit-or-tag>"
```


## Proof Style and Workflow

Source-facing theorems use direct propositions. The former `Std.Do.Triple`
wrappers over pure `Id` computations are retired; do not reintroduce them. A
concise playbook lives in `PIPELINE.md`.

- Preferred pattern: reduce executable specs to pure facts using small helper equalities, then discharge via `unfold`/`simp`/`calc`.
- Bool/Prop conversions: use `decide` when the spec relates boolean results to propositions.
- Tight loop: write one theorem, build fast, iterate.

See:

- `PIPELINE.md` – end‑to‑end notes, patterns, and pitfalls
- `FloatSpec/src/Core/Defs.lean` – small, self‑contained examples of specs and proofs
- `FloatSpec/src/Calc/Operations.lean` – alignment/arith operations with shape‑correct specs


## Roadmap

- Complete rounding and generic format lemmas in `Core/Generic_fmt.lean`, and ulp/rounding bridges in `Core/Ulp.lean`.
- Finish IEEE 754 bit‑level encodings/decodings and round‑trip theorems (`IEEE754/Bits.lean`, `IEEE754/Binary.lean`, `BinarySingleNaN.lean`).
- Close error‑bound theorems in `Prop` (`Plus_error`, `Div_sqrt_error`, `Double_rounding`, `Relative`, `Sterbenz`, `Round_odd`).
- Expand “calc” coverage (division, sqrt bracketing) from shape to fully verified correctness.
- Documentation and examples; add small sanity tests once more core proofs stabilize.
- VCFloat integration (ErrorBound): implement MVP per `docs/vcfloat_integration/TODOs.md` — Types/Knowledge, RExpr, make_rounding, absolute error lemmas, and two FPBench examples; then extend to relative lemmas and composition rules.


## Repository Layout

- `FloatSpec.lean` – root re‑exports and version
- `Main.lean` – placeholder executable entry point
- `FloatSpec/src/**` – library source (see Architecture)
- `FloatSpec/docs/vcfloat_integration/**` – design notes and TODOs for VCFloat‑style error‑bound integration
- `lakefile.lean`, `lean-toolchain` – build configuration
- `PIPELINE.md`, `CLAUDE.md` – proof workflow and notes
- `FloatSpec_status.pdf` – progress/status snapshot
- `LICENSE` – license information


## Contributing

Contributions are welcome. Please:

- Read `PIPELINE.md` first; follow the one‑proof‑at‑a‑time workflow and compile frequently.
- Keep changes focused; avoid broad refactors unless discussed.
- Prefer adding small helper lemmas over heavy `simp` configurations for arithmetic proofs.

Feel free to open issues with questions about proof strategies, missing lemmas, or module boundaries.


## License and Acknowledgments

- License: see `LICENSE` in the repository.
- Based on the Flocq project (Sylvie Boldo, Guillaume Melquiond). Ported and adapted to Lean 4 with Mathlib.
