# Response to Claude's independent cross-check

The [original report](CLAUDE_AUDIT_2026-09-21.md) is copied unchanged from
Claude's commit `ce19cf18` on `claude/audit-2026-09-21`. Its worktree was read,
not edited. Its reviewed production head is **60096e0c**, not the later main
head **a260583d**. Claude source-inspected the next 34 Round_pred laws, but did
not build that follow-up or audit the subsequent nearest-even totality commit.

Claude reports no semantic mismatch among approximately 150 anchored declarations
it compared premise-by-premise, plus independent builds, axiom inspection, seven
Rocq fixtures and a 90,804-case oracle spot check. Those are the reviewer's
reported executions, not newly repeated results from this response. They are a
useful independent cross-check, not a universal or whole-port equivalence proof.

## Disposition of the ten findings

1. **Hosted Rocq and differential execution: implemented; first hosted run timed out in the full grid.**
   The prior CI intentionally ran Lean and local harness checks, but its
   `skipUnless(FLOCQ_AUDIT_DIR)` tests were too easy to mistake for live conformance
   coverage. The new CI installs Rocq 9.1.0/Stdlib 9.0.0, builds the exact gitlink,
   runs pure Rocq fixtures and required live mutation suites, then executes a
   shared-input bridge with generated Lean kernel equalities. A dedicated runner
   rejects missing prerequisites, any skip, an empty suite, errors and timeouts.
   Artifacts retain reports, inputs, generated programs and logs for 30 days.
   Hosted success must be observed on the actual new revision before claiming it.
   Run `35670420386` verified installation, the reference build, Lean/Rocq
   fixtures and all required live tests, but hit the two-hour job limit during
   the oversized differential grid. That is not a passing run. The follow-up
   bounds the per-push grid explicitly, keeps all live mutation tests, stores
   evidence outside restored build caches, and saves the installed Rocq cache
   before long tests so a later timeout cannot discard toolchain setup.
   The failed run's downloadable artifact was inspected: it records **174 live
   tests with zero skips** (1345.821 seconds), and **20,600** compared/kernel-
   bootstrapped bridge cases before cancellation. Its bridge report still says
   `running`, so neither that report nor the cancelled job is counted as a pass.
   Historical `/private/tmp` receipts are not durable shared artifacts; however,
   the checked-in harnesses, replay inputs and documented seeds already support
   new executions against the pin. Re-execution is not recovery of an old receipt.

2. **Extensional versus structural Pff implementations: accepted, still open.**
   The source-link attribute checks navigation/provenance, not body identity or
   semantic equivalence. `Pdiv`, `Zquotient` and `ZdividesP` use Lean arithmetic
   primitives rather than a literal transcription of Coq's recursion. Their
   tested behavior and local correctness laws must not be presented as a closed
   cross-language structural-equivalence proof. Add structural reference bodies
   and prove the translations, or explicitly classify them in the review ledger
   when the source-order audit reaches this slice. No numerical body is rewritten
   solely to increase source-link counts.

3. **Missing submodule metadata: accepted.** `.gitmodules` now names the existing
   Flocq remote and path; it does not alter the gitlink or initialize/reset the
   user's modified local dependency. Standard fresh-clone initialization is the
   intended path. Digest validation of non-Git archives remains unimplemented;
   the current validator deliberately requires an exact clean Git reference.

4. **Legacy Hoare wrappers: accepted as API/maintenance debt, not a new math bug.**
   Prefer direct propositions as proof owners in future reviewed slices; retain
   compatibility wrappers only while callers require them. Existing direct
   theorems derived from faithful wrapper propositions remain valid Lean proofs.
   Do not mass-rewrite this layer without checking callers and source premises.

5. **Missing changed-fingerprint regression: fixed locally.** A positive control
   and three separate mutations now verify rejection of changed type hashes,
   value hashes and computability flags. This protects the existing gate; it does
   not claim to catch drift hidden solely in transitive dependencies.

6. **Stale manual theorem map: labeled historical.** The old comparison document
   now warns that removed names and line positions are stale and directs readers
   to the compiled queue and explicit review ledger. It is not regenerated from
   approximate name matches and called semantically reviewed.

7. **Docstring nits: accepted, queued.** The two fixed-choice payload helpers,
   misplaced private-helper documentation, positive-exponent wording and missing
   Fabs documentation should be corrected in the next source-documentation slice.
   The `round_to_generic`/`roundR` distinction mentioned in the report is
   definitional equality, not an observed difference in the rounded value.

8. **Exponent-boundary count: clarified.** The guide now says eleven paired
   propositions plus the zigzag exponent definition, rather than eleven total
   declarations.

9. **Test trust coverage: added a separate compiled-test gate.** The old compiled
   scanner indeed visited only `FloatSpec.src.*`.
   However, `check_proof_debts.py` scans all of `FloatSpec/`, including tests, and
   rejects unnamed/unapproved written `sorry`; the Lake package also enables
   `warningAsError`. Macro-generated admissions, suppressed warnings or transitive
   test dependencies are now checked with `check_compiled_trust.py --scope tests`,
   which imports every test module and allows no proof debt. The fresh audit
   passes 311 declarations across all 35 test modules with no trust hazards;
   the compiled scanner's deliberate hazard mutations still pass. Standalone
   fixtures outside this test tree are not included in that coverage claim.
   Ordinary `#eval` tests are runtime assertions, not
   kernel proofs, regardless of which directory contains them.

10. **Linear verification: observer limitation resolved separately.** Claude's
    connector was unavailable, so it correctly did not attest to Linear updates.
    This continuation successfully updated CFS-3 with the independent audit and
    its scope and CFS-2 with the complementary GwernPort job-update evidence.
    This does not retroactively make Linear a Claude-verified result.

## Fresh execution while responding

- On macOS Lean 4.34.0 and the existing Rocq 9.2 reference: all four
  Round_pred suite methods and all eight nearest-even mutation methods passed,
  including the Rocq halves, with zero skips.
- A separate clean checkout of the same Flocq pin was fully rebuilt using
  Rocq 9.1.0/Stdlib 9.0.0, the versions selected for CI. The original
  `Deps/flocq` remains untouched.
- All ten queue tests and all eight required-suite policy tests passed.
- A disposable fresh repository successfully initialized the submodule from
  the upstream network at the exact pin. All 456 current source anchors validate
  against the clean rebuilt Rocq 9.1 reference.
- All seven pure Rocq fixtures selected for CI pass with Rocq 9.1.
- The full required suite passes **174 tests, zero skips**, against that reference
  (1045.763 seconds including the runner's preflight). Fresh Lean arithmetic assertions, nearest-even clients and
  all seven demo examples pass. Production trust remains 13,778 declarations,
  59 modules and the same four debts; the new test scope has zero debts.
- The initial 35,594-case all-family bridge was interrupted for runtime budgeting
  and is not a pass. Per-push CI now uses the explicitly listed 4,309-case core
  profile plus four saved IEEE counterexample replays; the full live suite is
  retained. Full-family execution remains available separately.
- A fresh full macOS build completes successfully (6225 jobs). No mathematical
  Lean source or dependency configuration changed in this response; its source
  SHA remains `cd22873cb11cf2d8f72aa29e9050b8888aff63c8debbf1ca62d19642314626dd`.
- The bounded profile passes **4,309** compiled Lean/Rocq comparisons and generated
  Lean kernel equalities at seed 865509. All **292** permanent counterexample
  replays also pass (197 raw rounding, 87 raw overflow, four primitive comparison,
  four primitive conversion). These are new complete local runs with Rocq 9.1,
  not relabeled fragments of the interrupted larger run.
- Receipts: `/private/tmp/floatspec-ci-core-bridge-865509/report.json`,
  `/private/tmp/floatspec-required-rocq91-20260921.json`, and the four
  `/private/tmp/floatspec-ci-replay-20260921-*/report.json` files. These paths are
  local evidence; the follow-up hosted run must independently reproduce the
  checks and publish its own artifact before it is called green.

The next source-contract target remains the nearest-even parity/definition layer.
This response does not promote any unreviewed source entry to reviewed status.
