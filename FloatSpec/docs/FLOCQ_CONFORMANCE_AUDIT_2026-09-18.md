# Focused Flocq conformance audit — 2026-09-18

## Scope and claim boundary

- FloatSpec baseline: `158263e983ec3925e02b10f5b312498bf414e0f1`
  (`origin/main` at the start of this audit), plus the repairs on
  `codex/flocq-conformance-audit`.
- Flocq source: the repository's `Deps/flocq` gitlink at
  `7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`.
- Source was built in a separate, clean, detached checkout. The local
  `Deps/flocq` checkout is dirty and was not modified by this audit.
- This is a **targeted source/contract/behavior audit**, not a completed
  declaration-by-declaration equivalence proof. The earlier alignment plan
  contains 5,951 jobs, of which 27 had been reviewed in its recorded batch
  (see `FLOCQ_ALIGNMENT_REPAIR_CHECKLIST.md`). No whole-repository alignment
  score follows from these checks.

## Confirmed divergences and repairs

| Area | Pinned Flocq contract or observation | Baseline deviation | Repair and regression |
|---|---|---|---|
| `Round_pred.satisfies_any` | `src/Core/Round_pred.v:1382-1385` requires zero membership, negation closure, and a downward rounding point for every real. | Lean required only a single member of the format; the format theorems could prove this using zero alone. | Restored all three fields in `Generic_fmt.satisfies_any`, with equivalence transport and concrete generic/FLX/FLXN/FLT/FIX/FTZ instances. Lean build checks the new proofs. |
| `Calc.Plus.Fplus_core` | `src/Calc/Plus.v:35-41` uses total integer `Zpower` for both scales; at `(β,m1,e1,m2,e2,e)=(2,1,0,0,1,1)` the result is `(0, loc_Exact)`. | `β ^ Int.natAbs (e1-e)` uses `2` instead of `Zpower 2 (-1)=0`. | Uses `Zpower` in both branches, with existing correctness proof rewritten at its nonnegative-exponent preconditions. Paired Flocq/Lean zero and positive controls compile. |
| `Calc.Round.truncate_aux` | `src/Calc/Round.v:609-612` uses `Zpower β k`; `truncate_aux 2 (2,0,Exact) (-1)` is `(0,-1,Inexact Gt)`. | `β ^ Int.natAbs k` changed the negative branch. | Uses total `Zpower`, retains positive-domain proof via `Zpower_Zpower_nat`, and checks negative/positive controls on both sides. |
| NaN payload validity | `src/IEEE754/Binary.v:160-170` uses a positive payload and `digits2_pos(payload) < prec`. At precision 3, payload 4 is too wide; payload 3 fits. | The permissive `FullFloat` bridge accepted zero and used a numeric power comparison that admitted an extra bit. | `valid_binary_payload` requires positive payload and checks digit length. Lean tests cover 0, 4, and 3; Rocq tests check the bitlength boundary. This does **not** turn permissive `Binary754` into the proof-carrying source carrier. |
| `make_bound_Emin` | `src/Pff/Pff2FlocqAux.v:160`; the exported lemma does not retain the section's `1<p` premise (as confirmed by `Print make_bound_Emin`). `make_bound 2 0 (-1)` has exponent 1. | Lean theorem required `1<p`, excluding this valid call. | Removed the redundant premise and repaired 13 downstream named-argument calls. The zero-precision observation compiles on both sides, with Lean using the repaired theorem. |
| Simproc rewrite | `reduceZtruncNeg` should rewrite an actual `Ztrunc (-x)` goal. | It assembled an undersaturated `Neg.neg` expression; defining the simproc alone never exercised that branch. | Uses `mkAppM` to synthesize typeclass arguments. `FloatSpec/Test/SimprocRaux.lean` imports and fires it on a real-valued variable. |
| Proof-hole scan | A `protected axiom` introduces a trust assumption. | The old scanner recognized only a bare line-start `axiom`. | Scanner recognizes modifier-prefixed axioms and other trust escapes; a fixture requires `protected axiom` to fail the scan. |
| Test evaluation trust | `native_decide` delegates reduction to the native evaluator, adding a trust boundary. | Eight existing `FloatSpec/Test/LeanFloat.lean` examples used it even though their small propositions can be kernel-reduced. | Changed each to `decide` and compiled the module after each edit. The scanner now flags `native_decide`, with a failing fixture. |
| Legacy closure checks | Flocq's structural closure lives in `satisfies_any`. | `*_format_0/opp/abs_check` return only unrelated `Ztrunc` identities, while their prose claimed format membership/closure. | Corrected the prose and removed unused format-membership premises from these local arithmetic regressions. The actual zero/negation/rounding proofs are in the repaired `*_format_satisfies_any` contracts. |
| ErrorBound | This is proposed VCFloat integration, not a Flocq module. | README called six empty files an implemented layer. | README and aggregator now explicitly say they are empty import scaffolding. |

## Executable evidence

Run `scripts/test_flocq_conformance.sh` with Rocq, autotools, and the pinned
Lean toolchain available. It resolves `HEAD:Deps/flocq`, verifies a supplied
`FLOCQ_AUDIT_DIR` against the gitlink or creates a clean temporary worktree
(a temporary clone on a checkout lacking the nested repository), builds Flocq,
compiles the pinned Rocq observations, then builds the paired Lean module.
The script never resets the user's nested checkout. The protected-axiom and
native-decide scanner fixtures are in `scripts/test_audit_placeholders.sh`.

On this macOS host, Rocq compiled the pinned source and all paired Coq
examples. Lean's pinned `v4.34.0-rc2` Lake crashed locally before building,
so the Lean checks used installed `v4.34.0` with the *same locked dependency
revisions*. This is a local compiler-version caveat, not an assertion that the
rc2 build itself passed here. At the time, Linux CI still selected rc2; the
follow-up below supersedes that configuration. The source build emitted only Rocq deprecation notices in the
targeted examples.

Follow-up: `lean-toolchain` now selects stable `v4.34.0`, so plain `lake build`
and the test/executable targets run on this macOS host. The Mathlib and CSLib
source revisions remain at their reviewed rc2 pins; this change does not claim
that rc2 Lake was repaired. The most recent paired Flocq run used Rocq 9.1.0.

## Unresolved boundaries

### Definition-first follow-up on this branch

The source-shaped `Binary.valid_binary` now checks finite exponent bounds and
significand normalization and checks a positive, precision-bounded NaN payload.
The permissive `Binary754` compatibility carrier remains separate; its
conversion theorem requires a validity premise. `Binary.valid_binary_SF`
remains a legacy `true` bridge over unrestricted inputs; the source-shaped
predicate `valid_binary_SF_payload` is used for the source-facing conversion
postcondition. Replacing the legacy bridge requires migrating its callers and
possibly restricting its carrier.

`PrimFloat` now exposes raw-bit next-up/down operations, with finite/special-
value examples. The sign-flip, native `Float.frExp`, and native next-up/down
correspondence theorems are deliberately named `sorry` obligations recorded in
`proof_debts.json`. These statements compile, but no native-runtime theorem is
claimed proved. CI rejects any unregistered `sorry` or trust escape.

`@[flocq_source]` records a pinned path, line, and Coq name for six public
definitions in `BitsSourceFacade` and `Binary.valid_binary`. The opt-in
`linter.coqSource` warns on unmapped public definitions in an enabled module.
The `Source:` URL comments provide editor-clickable links to the pinned Coq
lines; the attribute string itself is not yet a go-to-source LSP action. This
is a first coverage gate, not a whole-repository map. No Rocq compiler or
coinduction translation is attempted.

The `Std.Do`/Hoare layer was separately reviewed: sampled float modules use
`Id` wrappers for pure operations, and no actual `mvcgen` tactic call was
found. Direct propositions are the simpler source-facing contracts. Existing
Hoare wrappers still have downstream callers, so any migration should be
incremental rather than a mechanical removal.

The first incremental migration is `Core/FIX.lean`: direct propositions now
state its format conversions, zero and negation closure, ulp, and integer
rounding result. Two IEEE callers were updated; the unrelated Boolean check
definitions and unused `@[spec]` annotations were removed. A CI guard keeps
the unused tactic surface out of the float sources. Most other modules still
contain legacy triples and have not been migrated.

1. The permissive `Binary754` compatibility carrier and its `binary_*`
   helpers are not equivalent to the proof-carrying `Binary.binary_float`
   operations. In particular, real-only compatibility arithmetic may lose
   NaN/infinity, signed-zero, and overflow behavior. Use the source-shaped
   namespace for correspondence; this audit did not replace the legacy APIs.
2. `Binary64.negated_toReal` proves semantic negation through `Bopp`, not the
   missing all-bit-pattern theorem
   `ofBits (flipSign w) = negated w`. Infinities and NaNs are collapsed by
   `toReal`, so real-value equality alone is insufficient.
3. `FaithfulPrimFloat.Z.frexp` and `next_up`/`next_down` are model operations
   transported through the proof-carrying carrier. Their `*_equiv` statements
   are model equalities, not native runtime `Float`/hardware equivalence.
   Model bridge theorems for other arithmetic do not imply these missing
   native-operation theorems.
4. The lexical placeholder scan is not an elaborated-environment axiom audit
   or proof of Flocq equivalence. A green Lean build establishes that the
   current Lean statements typecheck, not that every statement matches Coq.
5. The 5,951-job declaration plan and independent adversarial review remain
   open. Any untested declaration is **not observed**, not certified aligned.
