# Claude follow-up audit, 2026-09-22

**Scope.** The four commits after the 2026-09-21 audit head `60096e0c`:
- `a3a84b81` feat(rounding): complete Flocq predicate source interface
- `a260583d` fix(rounding): expose direct nearest-even totality contracts
- `b501cb14` ci: require pinned Rocq and Flocq cross-checks
- `ab738ab3` ci: bound cross-tests and close compiled test audit gap

Reviewed at `ab738ab3` in the isolated worktree `~/FloatSpec-audit-claude` (branch `claude/audit-2026-09-22`). The live checkout was not modified. Reference: pinned Flocq `7aab8f55`, a clean build at `/private/tmp/flocq-audit-rocq91-20260921` (Rocq 9.1.0, `_opam` switch).

## Results

### 1. Build
`lake build FloatSpec.Test FloatSpecTests floatspec` succeeds with 6,225 jobs. The build cache was cloned from the live checkout, and Lake re-verified every trace against the worktree sources.

### 2. Statement fidelity: mechanical, all anchored Round_pred and Round_NE exports

I generated a Lean `#check` and a Rocq `Check`/`About` for every `@[flocq_source "src/Core/Round_pred.v" …]` declaration (78) and for the three new Round_NE exports, then compared them side by side.

- **Round_pred: 77 theorems and definitions plus `satisfies_any`, all premise-for-premise identical to Rocq's compiled statements.** The only differences carry no meaning:
  - Binder order in `Rnd_DN_UP_pt_split`: Lean binds `f` before the `Rnd_DN_pt` hypothesis; Rocq binds it after the `Rnd_UP_pt` hypothesis.
  - Bound-variable names (`f g` vs `f1 f2`).
  - `Rnd_NG_pt_unique_prop`'s `P`: Rocq infers `R -> R -> Type`, Lean has `ℝ → ℝ → Sort u_1`.
- **`satisfies_any`:** both are `(ℝ → Prop) → Prop` with the same single constructor, so both admit large elimination. The queue's four `adapted-proof-infrastructure` entries map Rocq's generated `_ind/_rec/_rect/_sind` onto `satisfies_any.rec`, which is correct.
- **Round_NE `Rnd_NE_pt_total` / `_monotone` / `_round`:**
  - Rocq `About` gives `beta fexp {valid_exp exists_NE_}` at lines 263/306/331. Lean gives `beta [ValidRadix] fexp [Valid_exp] [Exists_NE]`. These match; `ValidRadix` is the Lean encoding of Rocq's `radix` subtype.
  - `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only.
- **Queue claims:** Round_pred is 83/83 (79 `reviewed-contract` plus 4 scheme adaptations) and Round_NE's new entries are 3/3. Both are consistent with the above.

### 3. Mutation controls (executed)
- `test_round_ne_point_contracts.LeanControls`: 4/4 pass.
- `test_round_ne_point_contracts.RocqControls` and `test_round_pred_contracts`: 8/8 pass against the pinned Rocq 9.1 build.
- `replace_once` enforces exactly one match. The unmutated fixture must compile, and each mutant must fail with a specific error class.
- The same test names appear in both `LeanControls` and `RocqControls`. Being in different classes, neither shadows the other (checked).

### 4. Response-document claims (spot-checked)
- `/private/tmp/floatspec-ci-core-bridge-865509/report.json`: `status=passed`, `cases=4309`, seed 865509, source SHA `cd22873c…`, as claimed.
- `/private/tmp/floatspec-required-rocq91-20260921.json`: `tests_run=174`, no skips, failures or errors, 1045.763 s, as claimed.
- `validate_flocq_source_refs.py` against the Rocq 9.1 reference: **456 anchors validate**, as claimed.
- Hosted run `35685386462` at `ab738ab3` is green (49 min).

### 5. CI / harness fail-open review (b501cb14, ab738ab3)

Verified OK:
- Every piped step sets `shell: bash`; the log shows `-e -o pipefail`. No `continue-on-error`.
- The runner fails closed on skips (including `setUpClass` `SkipTest`), empty suites, import errors, errors and interrupts.
- The Flocq pin is freshly cloned and built. `verify_reference` runs in both the runner and the bridge. Neither cache can mask a changed reference.
- Run `35685386462`'s log matches the response doc exactly:
  - 174 OK / 0 skipped;
  - 4,309 bridge cases / 0 mismatches;
  - 292 replays (197 + 87 + 4 + 4);
  - trust 13,778 / 59 / 4 for src and 311 / 35 / 0 for tests;
  - 7 Rocq fixtures with `Print Assumptions`.
- `check_compiled_trust` catches axioms, `unsafe`, `partial`, `implemented_by`, `extern` and the `native_decide` helper axiom in named declarations.

## Findings

**F1 (confirmed, medium): the required live suite omits 8 of the 24 `FLOCQ_AUDIT_DIR`-gated test modules, and nothing checks completeness.**
- `scripts/run_required_rocq_tests.py` `LIVE_MODULES` lists 16 modules.
- These have `FLOCQ_AUDIT_DIR`-gated tests but are not listed, and none of them appears anywhere in `.github/workflows/ci.yml`:
  - `test_pff_bridge` (20 methods)
  - `test_ieee_exact_oracle` (16)
  - `test_pff_aux_bridge` (8)
  - `test_model_adapter_bridge` (7)
  - `test_remainder_bridge` (6)
  - `test_double_rounding_contracts` (3)
  - `test_lpo_contracts` (2)
  - `test_pff_rounding_contracts` (2)
- Only `testsRun > 0` is enforced, so the count can fall below 174, or a new live module can be added and never run, and CI stays green.
- This contradicts `CLAUDE_AUDIT_RESPONSE_2026-09-21.md`: "keeps all live mutation tests" and "the full live suite is retained".
- *Fix:* derive the list by scanning `scripts/test_*.py` for `FLOCQ_AUDIT_DIR`. Alternatively, add a policy test asserting that `set(LIVE_MODULES)` equals the gated set, with explicit, documented exclusions. Also add a floor on `tests_run`.

**F2 (confirmed by code inspection and a subagent probe on Lean 4.34.0; latent, medium): `example` declarations are invisible to the test-scope compiled trust gate.**
- `example` elaborates without modifying the environment, so the `env.constants` loop never sees `FloatSpec/Test`'s 297 examples. The "311 declarations" figure counts named declarations only.
- `audit_placeholders.sh:88` matches only `\bnative_decide\b`, so `example … := by decide +native` passes every gate.
- An example containing `set_option warningAsError false in #guard_msgs(drop warning) in … sorryAx …` also passes.
- There is no current exposure: `rg` finds no `decide +native`, `native_decide`, `ofReduceBool`, `skipKernelTC` or `sorryAx` in `FloatSpec/` or `scripts/fixtures/`.
- This contradicts the response's claim that macro-generated admissions and suppressed warnings are now checked in tests.
- *Fix:*
  - Extend the text scanner to `decide\s*\+native`, `Lean.ofReduceBool`, `debug.skipKernelTC`, `sorryAx` and `set_option warningAsError false`.
  - Either convert test `example`s to named `theorem`s, or run the compiled scan on a copy where `example` is rewritten to a named private theorem.

**F3 (confirmed, low): the runner-policy tests are narrower than the docs say.**
- `THREE_VERIFICATION_LOOPS.md` says "eight runner-policy controls test these boundaries". None tests a dirty reference, a wrong pin, or a missing compiler.
- `verify_reference` diffs only `src/`, so local edits to Flocq build files or gitignored `.v` files would pass. This doesn't matter in fresh-clone CI; it does matter for local receipts.

**F4 (confirmed, low, predates these commits): standalone fixtures have no admission gate.**
- `scripts/fixtures/*.lean` run via `lake env lean`, which does not apply `warningAsError`, and `check_proof_debts.py` scans only `FloatSpec/`. A `sorry` or `native_decide` in a fixture would leave CI green.
- `.v` fixtures are not grepped for `Admitted`.
- None of these constructs is present today.

**Plausible / informational:**
- The 19 families excluded from the per-push bridge get 3 boundary cases each plus the saved replays; no scheduled job runs the full 35,594-case grid.
- About half the `.v` fixtures are not compiled in hosted CI; this count is approximate.
- `upload-artifact` uses `if-no-files-found: warn`.
- The gitlink equality check at `ci.yml:70` is a no-op straight after `git submodule update`; the real check is `verify_reference`.

The mathematical content of `a3a84b81` and `a260583d` is faithful. All findings concern harness coverage and the accuracy of the response doc's claims.
