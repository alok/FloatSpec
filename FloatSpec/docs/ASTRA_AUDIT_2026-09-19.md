# Independent continuation audit — 19 September 2026

This is a running evidence record, not a declaration that the port is correct.
Read [the linear guide](READING_GUIDE.md) first for the mathematical structure.

## Baselines and preservation

The review starts from `d4c44d9b3ae217211bff53fc4f06da3d91424e60`, on a new
`codex/astra-flocq-audit` branch. It includes the 23 Codex commits from upstream
`158263e983ec3925e02b10f5b312498bf414e0f1` through `10bd939f`, plus Claude's
subsequent FTZ equivalence proof. Upstream `main` was checked live and still
pointed to that baseline. The modified nested `Deps/flocq` checkout is preserved.

The reference is the parent repository's Flocq gitlink,
`7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`, not the nested checkout's current
HEAD. Executions use a separate detached reference checkout.

## Confirmed checks and findings

1. **Fresh macOS baseline build passed:** Lean 4.34.0, arm64,
   `lake build FloatSpec.Test FloatSpecTests floatspec` (6,207 jobs).
2. **The Claude FTZ proof is genuinely closed:** fresh LSP diagnostics passed;
   `#print axioms FloatSpec.Core.FTZ.FTZ_format_iff_generic` reported only
   `propext`, `Classical.choice`, and `Quot.sound`, not `sorryAx`. The structural
   format predicate was compared with pinned `Core/FTZ.v:36`; it retains the
   nonzero normalized-mantissa and minimum-exponent requirements. This does
   not audit all downstream theorem statements. Four native/bit bridge debts
   remain in the manifest.
3. **Source-link gate bypass reproduced and repaired:** a mutual block with a
   classified first definition and unclassified second definition passed the
   old strict linter. The scanner selected only its first declaration. It now
   visits every written definition, checks privacy only in its modifiers, and
   handles root-qualified names. Executed positive and negative fixtures cover
   mutual members, a private first member, abbreviations, and qualified names.
   Link classification remains metadata, not semantic equivalence.
   The post-fix aggregate build passed again (6,207 jobs), and the existing
   paired Flocq examples passed with the configured Homebrew Rocq 9.2 compiler.
   The shell's other `coqc` is Rocq 9.1 and cannot load that checkout's `.vo`
   files; the bridge must resolve the compiler from `config.status`.
4. **The old paired tests are not a differential harness:** they execute small
   hand-written Lean and Rocq example sets independently. The new shared-input
   bridge replaces that coverage gap; do not retroactively treat the old test
   name as evidence of randomized or exhaustive cross-testing.
5. **Three executable loops now pass on macOS:** the standalone Lean and Rocq
   grids each check 10,734 independent arithmetic-invariant cases. The new
   differential runner passed 4,247 cases (seed `20260919`) and then 10,736
   cases (seed `483921`). After adding bootstrapping, a full three-loop run
   passed 4,996 differential cases (seed `20260919`, 200 random samples per
   family), and all 4,996 generated Lean equality statements checked in the
   kernel. These runs used the cached Rocq 9.2 reference. The three Lean grid
   theorems have no `sorryAx`: division uses no axioms; location and square
   root use only `propext`. The aggregate build now passes 6,208 jobs.
   A second full three-loop run built **all pinned Flocq from scratch** under
   the project-local Rocq 9.1.0, then passed both invariant grids, 4,247 bridge
   cases and their generated Lean proofs, and all nine harness tests. The
   clean reference worktree was removed afterwards; the user's nested checkout
   and its untracked dependency-graph files were unchanged. `lake exe floatspec`
   also ran, but its no-op `main` is only a launch check, not an arithmetic test.
6. **The bridge fails closed:** the initial run correctly rejected abbreviated
   `#reduce` output containing `⋯`; full pretty printing resolved it. A second
   setup failure exposed missing `ValidRadix 3` instances, fixed with proved
   local instances for each test radix. Neither failed run is counted as a
   pass. Live mutation testing changes the historical `2^(-1)` case to use
   `natAbs` in the generated Lean input; the runner detects Lean `[2]` versus
   Rocq `[0]`, exits unsuccessfully, and writes an exact replay corpus.
7. **A second trust-gate bypass is repaired:** valid Lean declarations written
   as `@[simp] public axiom ...` or `public axiom ...` compiled, yet the old
   scanner returned zero findings. The declaration prefixes now cover public
   and meta modifiers and inline attributes; actual `@[extern ...]` attributes
   are recognized too. Compiled negative fixtures verify both cases. No such
   active axioms were found in the port during this check. Separately,
   `--diff --json` failed on macOS because it used a GNU-only three-argument
   `awk match`; the portable form now executes successfully. The scan remains
   an explicitly documented heuristic, not a full Lean environment audit.
8. **Higher-level execution coverage expanded:** 2,212 cases across digit
   counts, format exponents, primitive operations, and format-dependent
   addition/division/square root/truncation agreed with pinned Rocq (seed `7831`,
   100 random samples per new family); all became checked Lean regressions.
   An earlier larger run hit a 120-second timeout checking a single enormous
   generated equality and is recorded as an error, not a pass. Generating one
   equality per case removed that bottleneck for the completed run. Adapters
   explicitly translate the precision/minimum-exponent parameter order; no
   product definition was changed merely to fit an incorrectly ordered test.
   The subsequent full twelve-family run passed **7,564** shared cases and
   all 7,564 generated kernel checks (seed `20260919`, 200 random samples per
   family, batches of 100), plus both independent grids and nine harness tests.
9. **Native IEEE three-way execution now passes:** **622** binary64 inputs
   agreed between native Lean execution, the Lean logical carrier, and pinned
   Rocq wherever the native contract applies. The corpus contains 308
   subnormals, 298 normals, two signed zeros, two infinities, and twelve NaNs;
   all 622 model/Rocq results became kernel-checked Lean equalities. NaNs are
   explicitly canonicalized; payload preservation is not claimed. The sixteen
   zero/nonfinite inputs retain their native `frExp` observations but do not
   assert that operation's out-of-contract equality: native exponent `0`
   differs from model/Rocq `-2101`. Their other fields still match, and the
   model agrees with Rocq on all fields. Seven harness tests pass, including
   live substitution of predecessor for successor that must fail with replay.
   An initial generated `IO.println` expression had missing parentheses and
   failed compilation; that run remains an error, not a pass. The permanent
   minimum-subnormal model theorem depends only on standard axioms
   (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx`.

10. **A source-facing validity theorem was vacuous:** the exported
    `BinarySingleNaN.binary_overflow_correct` used the always-true legacy
    `valid_binary_SF` predicate. Its statement and root implementation now use
    `validBinarySingleNaNStandardFloat`, matching pinned
    `IEEE754/BinarySingleNaN.v:1195`. An existing private proof supplies the
    stronger result; no sorry was needed. A typed consumer regression prevents
    accidental reversion, and malformed finite inputs are explicitly rejected.
    All **390** new overflow cases (seed `34781`) agree with Rocq and became
    checked Lean equalities: five modes, both signs, small precisions and the
    usual 24/53-bit formats. Inputs enforce the source premises
    `0 < prec < emax`; this run does not assert out-of-domain equivalence.
    Axiom inspection of the exported theorem reports only standard axioms.
11. **An extra rounding premise narrowed a source theorem:**
    `FIX.round_FIX_IZR` required `[Valid_rnd f]`, although the pinned source
    theorem quantifies over every `f : R -> Z`. Removing the premise preserves
    its existing proof. The regression now works for arbitrary `f` and for the
    deliberately invalid rounding function `fun _ => 7`.

See [the three-loop guide](THREE_VERIFICATION_LOOPS.md) for commands, output
artifacts, and current coverage. No arithmetic algorithm was changed to make
these new tests pass. Repairs include the source-link/trust gates and the two
source-facing theorem signatures above.

## Prior-commit review ledger

The table tracks the **changed surfaces**, not certification of all declarations
in each affected file. “Checked” means the named definition/statement was read
against pinned source and exercised by the described build/tests; it does not
mean a universal cross-assistant equivalence theorem exists. The two broad
initial commits remain partially reviewed because their tooling and legacy
compatibility boundaries have more surface than the focused later changes.

| Prior commit | Changed surface checked | Boundary / finding |
|---|---|---|
| `f10d70b1` | `satisfies_any`, signed powers in Plus/Round, format closure contracts, Pff minimum exponent, native/model claim split | Partial broad review; scanner bypass repaired; old paired tests were not a shared-input bridge. |
| `c50fdb3a` | FullFloat validity against Binary.v; source-link metadata; native bit operations and four explicit proof obligations | Partial broad review; mutual-block linter bypass repaired; raw sign-bit proof still open. |
| `0de3c3bf` | Toolchain changed from 4.34 RC2 to stable 4.34.0 | Actual arm64 macOS builds pass; dependency pins were not silently upgraded. |
| `e500d138` | Removal of unused mvcgen/Hoare lint surface; direct FIX contracts | Unnecessary `Valid_rnd` premise found and removed; no new proof framework required. |
| `0fdc837d` | Defs predicates and source-anchor validation | Defs predicates match the source forms read; anchor validator remains textual/heuristic. |
| `4800ce00` | FLX generic/structural format conversions | Hypotheses and implications checked; generic-format equivalence is not merely renamed identity. |
| `5447ff8a` | FLX/FLXN source links and explicitly local helper labels | Metadata classification is not a proof of correspondence. |
| `653175ac` | FTZ normalized witness and exponent lower bound | Matches FTZ.v:36; the temporary proof debt was closed later by Claude. |
| `5ffe7a86` | FLT structural witness and generic conversion statements | Matches bounded mantissa/minimum-exponent source form; legacy arithmetic probes remain clearly separate. |
| `62e58771` | FLXN conversion and FIX/FLX inclusions | Source interval endpoints and precision premises checked. |
| `33102927` | FIX witness with exponent exactly `emin` | Matches FIX.v:34; zero/negation and both generic conversions checked. |
| `70705e9d` | Plus source metadata | Actual Plus operation also participates in shared-input tests. |
| `f8b288a4` | Close-magnitude addition now calls `Operations.Fplus` | Source branch checked; tested through combined format-dependent operations. |
| `75655bb0` | Operations definitions and metadata | Alignment, sign/abs, addition/subtraction/multiplication cross-tested. |
| `9a9b6c1c` | Direct alignment and same-exponent statements | Compared with Operations.v:44,59,111,143; no added mathematical premise. |
| `f2e8f192` | Canonical `truncate` signature and precision-dependent binary shift | Source Round.v:638 input triple/exponent function restored; callers rebuilt and format-dependent truncation cross-tested. |
| `454ba287` | Round source names and mode decisions | Source helpers exercised over sign/location combinations; duplicate local helpers are not separate algorithms. |
| `8fd2639d` | Direct positive-quotient correctness | Source Div.v:132 retains both positivity hypotheses; radix premise comes from `ValidRadix`. |
| `bb24499f` | Square-root contracts | Source Sqrt.v:73,179 positivity/shift premises checked; negative total-function cases tested separately. |
| `495d815e` | Bracket link gate and interval specification | Source Bracket.v:38,50 checked; even/odd functions have independent rational-grid tests. |
| `3e3749e9` | Direct Bracket uniqueness and bounds | Source Bracket.v:63,82,94 checked; strict interval hypothesis retained where required. |
| `8fd8bb36` | Direct inexact distance comparisons | Source Bracket.v:106,116 checked; removed identity-returning wrappers. |
| `10bd939f` | Direct existential interval witness | Source Bracket.v:135 checked; downstream float witness updated coherently. |
| `d4c44d9b` (Claude) | Both FTZ conversion proof directions | Proof structure compared with source; fresh kernel build and standard-axiom check passed. |

## Execution priorities

Maintain three separate loops: independent Lean tests, independent pinned
Flocq/Rocq tests, and a differential bridge that sends identical inputs to both.
Record concrete cases and seeds; promote disagreements to permanent regression
examples. Keep valid theorem domains distinct from total-function behavior
outside those domains. Test the bridge with intentional mismatches so a parser
or skipped command cannot silently produce a green result.

## Still unreviewed

The bulk of the complete theorem-by-theorem port remains unreviewed. In
particular, root compatibility predicates such as `valid_binary_SF := true`
still exist: the repaired overflow export does not certify every legacy user
of that predicate. The source-anchor scanner is textual, the linter is opt-in,
and many public declarations are outside its current gate. Next work includes
native execution of integer-only algorithms, more IEEE arithmetic cross-tests,
and further source-signature checks. Passing compilation, finite agreement,
and a proof of a Lean statement are three different claims; none alone proves
whole-library Flocq equivalence.
