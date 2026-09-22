# Independent audit of the Codex (astra) continuation, September 21, 2026

Reviewed head: `60096e0c` (`feat(rounding): restore direct Flocq predicate
contracts`) on `origin/main` (github.com/alok/FloatSpec). Scope: every source
commit from the Claude integration merge `65f8ab5f` through `60096e0c`, plus
the earlier ULP/Generic_fmt/Raux contract repairs (`3bfb3a68` … `0a448328`,
`5a6d16df`, `7070f6f0`) that the reading guide relies on. Reference: pinned
Flocq `7aab8f55` (the `Deps/flocq` gitlink), exported with `git archive`, and
for the ULP slice a scratch Rocq build of that pin so that `About` could report
the *compiled* premise sets rather than the section text.

The audit ran in a separate worktree (`~/FloatSpec-audit-claude`, branch
`claude/audit-2026-09-21`) so that the live `main` checkout, which Codex was
still editing during the review, was never built or modified.

## Verdict

The work is faithful and well-evidenced. No semantic mismatch with the pinned
Coq statements was found in any of the ~150 anchored declarations that were
compared premise-by-premise. No new `sorry`, project axiom, `native_decide`,
`unsafe`, or `implemented_by` was introduced; every checked declaration depends
only on `propext`, `Classical.choice`, `Quot.sound`. The numeric claims in the
docs that could be checked against the diffs are accurate. The findings below
are about labeling honesty, test-coverage gaps, and repository hygiene, not
about wrong mathematics.

## What was reproduced here

| Check | Result |
|---|---|
| `lake build FloatSpec.Test FloatSpecTests floatspec` at `60096e0c` | 6225 jobs, success |
| `lake exe floatspec_demo` | all seven examples pass |
| `#print axioms` on the 25 new/repaired Round_pred exports | standard axioms only, no `sorryAx` |
| `#print axioms` on 71 changed ULP/Generic_fmt/Raux/Div_sqrt_error declarations | standard axioms only |
| `#print axioms` on the 12 raw/canonical comparison bridges and the `maxDiv`/`iter_pos` equality proofs | standard axioms only |
| `check_proof_debts.py`, `check_compiled_trust.py --skip-build` | 4 named debts, transitive sorry set == manifest, 13,720 declarations / 59 modules |
| Lean halves of `test_round_pred_contracts`, `test_zaux_power_contracts`, `test_zaux_division_contracts`, `test_pff_basic_contracts`, `test_pff_integer_bridge`, `test_round_ne_point_contracts`, `test_ulp_nearest_contracts`, `test_ulp_choice_contracts`, `test_remainder_contracts`, `test_lpo_contracts`, `test_flocq_port_queue` | all pass; Rocq halves skipped (no `FLOCQ_AUDIT_DIR`) |
| Rocq fixtures `UlpNearestChoiceContracts.v`, `CorePremiseBoundary.v`, `UlpSourceChoice.v`, `LpoSourceContracts.v`, `RemainderContracts.v`, `ExponentValidityBoundary.v`, `SourcePremiseContracts.v` compiled against a scratch build of `7aab8f55` | all exit 0 |
| Oracle spot check: 90,804 RNE add/sub/mul/div/sqrt results from `ieee_exact_oracle.py` vs hardware binary64 | 0 mismatches |
| Hosted CI run 35635101867 for `60096e0c` | completed, success (build, regressions, trust, status, hygiene) |

## Statement-level review by slice

### Round_pred direct laws (`60096e0c`) — 25/25 faithful

Every statement at `src/Core/Round_pred.v:89–539` was compared with the Lean
export. All premises, conclusions and line anchors match, including the two
subtle ones: `Rnd_N_pt_monotone` keeps the strict `x < y`, and
`Rnd_N_pt_unique` keeps `x - d ≠ u - x`. The `{−1, 1}` counterexamples in the
paired fixtures are genuine. The five repaired "Coq-compatible name" exports
(`Rnd_DN_UP_pt_split`, `Only_DN_or_UP`, `Rnd_N_pt_DN_or_UP`,
`Rnd_N_pt_DN_or_UP_eq`, `Rnd_N_pt_opp_inv`) had no callers outside the new
fixture. The bridge proofs via the legacy `*_check`/`*_spec` pairs are sound,
not vacuous: the checks decide exactly the stated proposition.

Codex's uncommitted follow-up (34 further Round_pred laws and the tie-policy
fixture) was inspected read-only against the Coq text at each cited line and
also matches; it was not built or tested here because it is not committed.

### Zaux (`9771f213`, `a0fd6e45`, `aeae41fa`) — 32/32 anchors faithful

`iter_pos` now has SpecFloat's binary-positive structure, with a closed
`iter_pos_nat` bridge to the previous semantics (`[propext]` only). The 54
removed `*_check`/`*_spec` wrappers have zero remaining references in any
`.lean`, `.py`, `.sh`, `.v` or `.toml` file. Floor vs truncating vs Euclidean
division is handled correctly: `ZO*` laws use `tdiv`/`tmod`, and the `Z.div`
laws that use Lean `/` only do so under nonnegative-divisor premises where the
two agree.

### Pff source facade and integer execution (`e1af393b` … `c3972539`) — 21/21 anchors faithful

The radix hypotheses were checked against what Coq's section mechanism
actually abstracts: the `definitions` section declares `1 < radix` but
`Fzero`, `is_Fzero`, `FzeroisReallyZero`, `is_Fzero_rep1` never use it, so
Coq exports them radix-free; `is_Fzero_rep2` does use it and Lean keeps it.
The `operations` section carries only `0 < radix`, so the claim that
`Fplus_correct`/`Fminus_correct`/`Fmult_correct`/`Fabs_correct` hold at radix
one is correct. `maxDiv` keeps Coq's structural recursion with `ZdividesP`
replacing `Classical.propDecidable`; the equality proof against the old
definition is closed. `Zquotient`, `Pdiv`, `oZ`, `oZ1` bodies are byte-identical
before and after the `noncomputable` removal. `round_NE_pt` is now the direct
`Rnd_NE_pt … (round … ZnearestE)` proposition with both Pff callers migrated.

### ULP / Generic_fmt / Raux / Div_sqrt_error repairs — 71/71 faithful

The eight nearest ULP contracts now quantify over `choice : Int → Bool` and
conclude about `round … (Znearest choice)`, matching Ulp.v; `round_N_ge_midp`
derives from `round_N_le_midp` with the transformed choice exactly as Coq.
The 27 dropped `Valid_exp` premises are absent from the compiled Coq types
(an `About` sweep found `Valid_exp` only on `round_NE_abs`, `round_N_eq_DN`,
`round_N_eq_ties`). `LPO`, `LPO_min`, `LPO_Z` are proof-carrying `PSum` of a
subtype, matching Coq's `{n | …} + {∀ n, ¬P n}`. The remainder lemmas carry
`Valid_exp`, `Monotone_exp`, and the verbatim small-quotient hypotheses, and
the zigzag counterexample genuinely separates `Valid_exp` from `Monotone_exp`.

### IEEE comparison and tooling (`ae042adf`, CI commits)

`FloatSpec/src/IEEE754.lean` does not import `ComputableCompare`; only the
test target and the audit exporters do, so the raw `SFcompare`-shaped API is
the default. The twelve `*_eq_raw*` bridge theorems are closed and their
canonicity hypothesis is `specFloat_bounded` = Flocq `bounded` with `Zdigits`
for `digits2_pos`. The exact IEEE oracle's NaN-priority, signed-zero, sqrt and
division semantics match `Bits.v` / `BinarySingleNaN.v`. The review-drift gate
does fail on a changed statement (verified by mutating a fingerprint in
memory).

## Findings

Ordered by how much they matter for "a pretty faithful port".

1. **Hosted CI proves Lean-only claims.** Every Rocq-side mutation test and
   every differential bridge is `@skipUnless(FLOCQ_AUDIT_DIR)`; hosted CI
   reports `OK (skipped=N)` with exit 0. The "three loops" evidence lives in
   local receipts under `/private/tmp/...` that nobody else can replay. The
   ULP reviewer here rebuilt the pin and compiled seven `.v` fixtures in about
   ten minutes, so a hosted Rocq job is feasible. Until then the docs should
   say "Lean gates hosted; Rocq gates local" in one place instead of per-slice.
2. **Three `flocq_source` anchors are extensional, not structural.**
   `Pff.lean` `Pdiv` (Nat `/`,`%` on a predecessor-encoded `Positive`),
   `Zquotient` (`Int.tdiv`) and `ZdividesP` (`Int` dvd decidability) are
   reimplementations that agree with Coq's `Fixpoint`/sign-split/`Z_eq_bool`
   bodies by test and by `Pdiv_correct`, but the attribute validates only
   path/line/name. Either add a distinct marker (e.g. `flocq_source_ext`) or a
   closed extensional-equality theorem against a structural transcription, so
   readers can tell "same body" from "same function".
3. **`Deps/flocq` is a gitlink with no `.gitmodules`.** `git worktree add`
   and fresh clones get an empty directory; `git submodule status` errors.
   The conformance script works around it by creating its own worktree from
   the gitlink, and `validate_flocq_source_refs.py` refuses anything but a git
   checkout at the pin, so a read-only source export cannot be validated. Add
   `.gitmodules` (or document the archive workaround) and give the validator
   a digest mode.
4. **The legacy Hoare/Boolean surface is still the majority of the library.**
   1,417 `⦃⌜…⌝⦄` triples remain in `FloatSpec/src` (Pff.lean 709, Raux 173,
   Ulp 101, Round_pred 74, Digits 67, Binary 51, BinarySingleNaN 44, Zaux 39).
   In Round_pred the direct laws are proved *from* the `*_spec` wrappers, so
   each law now has three encodings and the mathematics lives in the
   least-readable one. Recommend inverting the dependency (direct theorem owns
   the proof, `*_spec` becomes a one-line corollary) as each file is reviewed,
   then deleting wrappers once callers migrate, as was done in Zaux.
5. **Drift-gate test coverage gap.** `test_flocq_port_queue.py` covers
   missing/empty/`None` fingerprints but not a *changed* hash; the gate itself
   works (verified). Add the one-line test.
6. **Stale generated doc.** `FloatSpec/src/Core/Core_Theorems_Comparison_Manual.md`
   still lists 28 of the 54 removed Zaux `*_spec` names.
7. **Docstring nits.** `Ulp.lean` `round_N_le_midp_from_fixed_choice_payload`
   and `..._ge_midp_...` still claim to be the Coq theorems; a stray
   `not_FTZ_generic_format_ulp` docstring attaches to a private lemma;
   `Zpower_pos_gt_0` says "natural number" for a `Positive`; `SourceFacade.lean`
   `Fabs` lacks a docstring; `round_N_le_midp` states its conclusion with
   `round_to_generic` while siblings use `roundR` (defeq).
8. **Count nit.** "Eleven paired exponent-boundary declarations" is twelve
   including the `zigzag` definition.
9. **Compiled trust scope.** `AuditCompiledTrust.lean` filters on
   `FloatSpec.src.`; a `sorry` under `FloatSpec/Test/**` would only warn.
10. **Linear was not checkable** from this session (connector unauthorized),
    so the "Linear CFS-3 updated" claims are unverified.

## Not verified here

Case counts, seeds, timings and the `/private/tmp` receipts cited in the
ledgers; the Rocq halves of the mutation tests via the project's own harness
(the fixtures were compiled directly instead); whole-library source
equivalence, which the docs correctly never claim.
