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
12. **Ordinary binary64 arithmetic could not practically execute:**
    `binaryPositiveOfNat` used `n-1` successor calls to construct a binary
    positive integer. Reducing even `1.0 + 1.0` or `sqrt 1.0` exhausted the
    recursion limit at actual 53-bit mantissas. Binary recursion now replaces
    unary counting; the public signature and `binaryPositiveOfNat_spec` remain
    unchanged and proved, with only standard axioms. The closed 53-bit
    conversion and the `1.0`/`2.0` arithmetic row now check in the kernel.
    This defect predates the reviewed Sol commits (`c55f38059`, August 27).
    A new persistent three-way arithmetic bridge and paired Lean/Rocq fixtures
    cover all five basic arithmetic operations at native binary64 sizes.
    Its first complete run passed **1,424 operand pairs** (seed `526913`,
    1,024 fixed boundary pairs plus 400 random/cancellation/adjacent pairs).
    All seven fields agreed, and all 1,424 model rows became kernel-checked
    equalities. The run includes every exceptional-operand combination, both
    signs of zero, normal/subnormal boundaries, underflow, overflow, and ties.
    Seven arithmetic-harness tests pass, including a live operand-swap mutation.
    The original Rocq fixture omitted the mode module import and failed its
    first harness run; that setup error was corrected before the passing run.
    A fresh compiled-environment check of 13,595 product declarations found no
    axiom or unsafe declarations and exactly the four named direct sorry
    dependencies. The scan includes theorem/opaque bodies (`value? true`);
    the default `value?` omits them and is not a valid proof-debt check.
    The aggregate macOS Lean 4.34.0 build (`FloatSpec.Test`, `FloatSpecTests`,
    and `floatspec`) subsequently passed all 6,210 jobs. The arithmetic
    harness was rerun after the source-snapshot guard was integrated.
13. **A concurrent rebuild invalidated an audit run:** the seed-8491
    9,145-case combined run stopped after 8,100 completed comparisons when a
    rebuilt `Binary.olean` was temporarily unavailable. The artifact
    `floatspec-bridge-cdil8tim/report.json` records `error`; it is not a full
    pass. Future evidence runs must hold imported Lean sources/build outputs
    stable. Simulated timeout and interruption tests now also explicitly
    require `error` in the arithmetic and core bridge reports.
    All bridges now fingerprint Lean sources and dependency configuration
    before building and check that fingerprint after the build and each batch.
    A simulated concurrent source change is rejected before any completed case.
    This guards edits, not arbitrary external replacement of compiled files.
14. **Textual source-anchor validation missed real attributes:** a compiled
    fixture with `@[inline, flocq_source ...]` and a subsequent
    `attribute [flocq_source ...] name` command was invisible to the old regex,
    while a commented-out annotation was counted. The default gate now builds
    the root import and exports Lean's persistent source-reference extension.
    It validates all **55** compiled references and checks the extension's
    pinned commit against the parent gitlink. The regression rejects a real
    missing Coq source while ignoring the comment. The optional `--lean-dir`
    mode remains explicitly labeled a legacy textual heuristic. None of these
    anchor checks establish body/type equivalence or require classification
    outside modules that opt into the linter.
15. **Another tautology occupied a source theorem name:** the old root
    `valid_binary_SF2FF` compared the conversion's validity with
    `valid_binary_SF_payload`, defined by the same expression. The source
    `Binary.v:173` instead compares independently defined FullFloat and
    SingleNaN validity. The source name now exports that direct equality from
    `BinarySingleNaN.lean`; the old wrapper has an explicit `_compat` name.
    The proof uses constructor cases and retains only the source's non-NaN
    premise, not an input-validity premise. A typed consumer regression and
    malformed-zero-mantissa example pass; no additional sorry is needed.
16. **The bit decoder duplicated the unary-counting conversion:** even after
    fixing the arithmetic converter, `bits_of_b64 (b64_of_bits 1.0_bits)` still
    exhausted kernel recursion. `Bits.lean` now shares the proved bit-recursive
    conversion. Its general, binary32, and binary64 decoders also compile
    after removing unnecessary `noncomputable` markers without changing their
    bodies/types. Compiled Lean runs 20,000 independent bit roundtrips, with
    kernel examples for ordinary values and signed signaling NaN payloads.
    The matching pure Rocq 20,000-check grid also passed. The direct decoder
    bridge passed **1,134** cases (seed `834782`): all nine fields agreed in
    compiled Lean, kernel reduction, and Rocq, and all 1,134 expected rows
    were subsequently kernel-checked. These include negative and over-width
    integer inputs and preserve NaN sign/payload data. Report artifact:
    `floatspec-bridge-eiz5sf98/report.json`.
17. **Core differential tests now check compiled Lean as well:** twelve
    integer-only Calc definitions/aliases were needlessly noncomputable.
    Removing just those markers enables all fifteen core bridge families to
    run compiled Lean, kernel reduction, and pinned Rocq. The two new families
    directly observe bit decoders rather than decoding through Float.Model.
    Fourteen harness tests pass, including a compiled-only mutation that is
    rejected even when kernel/Rocq agree. Initial Rocq adapter compilation
    exposed omitted explicit `B2FF` format parameters; those were corrected
    before the passing harness run, not hidden as skipped comparisons.
    The aggregate macOS Lean 4.34.0 build passed **6,211 jobs**; source-link,
    placeholder, unused-mvcgen, and proof-debt gates passed, and the fresh
    compiler-backed anchor validator checked all **56** references.
18. **Compiled trust evidence is now reproducible:** the new compiler audit
    inspected **13,577 declarations in all 58 source modules**. It found no
    project axioms, unsafe declarations, custom runtime overrides, or
    dependencies on axioms beyond `propext`, `Classical.choice`, `Quot.sound`,
    and the four declared `sorryAx` debts. Exactly those four declarations
    depend on sorry even transitively; no wrapper silently propagates them.
    Two harness tests pass, including a compiled fixture containing theorem
    and opaque sorries, a wrapper around a sorry, a project axiom, an unsafe
    definition, a `native_decide`-generated axiom, and both
    `extern`/`implemented_by` overrides. The checker
    rejects missing source-module coverage and mismatched manifest names.
    This supplements the lexical gate and does not certify compiler/FFI
    semantics or the correctness of the source-facing mathematical statements.
    The expanded core run on source commit `3cb6d0a3` subsequently passed
    **9,879 cases** (seed `8491`) in all three evaluators, with all 9,879
    bootstrapped kernel equalities. Artifact: `floatspec-bridge-ijq9bfmq`.
    The aggregate seed-`8491` run then completed successfully: **1,022** native
    unary cases (298.538 seconds), **1,424** native arithmetic pairs
    (1,220.391 seconds), all corresponding generated kernel equalities, and
    all live harness tests. Native artifacts are `floatspec-native-ieee-j8xtyw3o`
    and `floatspec-native-arithmetic-srb2let1`. This receipt uses the stable
    product snapshot `cea9a82a…` and the then-existing fifteen core families;
    it does not include later order/bit-field families or the subsequently
    integrated all-mode/trust phases.
19. **Directed rounding and payload-sensitive arithmetic are now tested:**
    a standalone source-API bridge passed **290 boundary triples** across
    binary32/binary64 and all five rounding modes. It checks exact input bits,
    add/subtract/multiply/divide/sqrt/FMA results, retaining NaN signs and
    payloads rather than taking a quotient. All 290 rows became kernel-checked
    equalities. Artifact: `floatspec-ieee-modes-0xd58h1c` (seed `923451`, zero
    additional random samples). Five harness tests pass, including changing
    upward rounding to nearest-even only on the Lean side and verifying the
    resulting replay case. This path runs the actual source-shaped decoders
    and operations, but is kernel/Rocq execution, not native directed rounding.
    The expanded run subsequently passed **590 cases** (seed `924857`,
    30 random triples per width/mode plus boundaries), with all 590 generated
    kernel equalities, in 939.901 seconds. Artifact:
    `floatspec-ieee-modes-37fz_hlr/report.json`.
20. **Integer-width bit interfaces have a separate execution slice:** the
    existing source facade, unlike the root natural-width helper, preserves
    negative widths and the corresponding right-shift/zero-power behavior.
    All **836 cases** (seed `593873`, 500 random cases after 336 boundaries)
    agreed in compiled Lean, kernel reduction, and Rocq, and all 836 expected
    rows passed generated kernel proofs. Artifact:
    `floatspec-bridge-ykxsmrng/report.json`. A targeted live harness regression
    checks negative right-shift rounding and zero moduli; the nine non-live
    parser/coverage tests also pass. This run reused the already built stable
    product snapshot explicitly (`fresh_build: false`), without changing or
    rebuilding product files underneath the concurrent native runs. The
    operation bodies and theorem contracts were not changed.
21. **The linear reading guide now follows one computation:** a small
    halfway-rounding example leads through representation, integer algorithms,
    theorem contracts, the three execution loops, and remaining review scope.
    Detailed historical per-module findings remain in the audit ledgers.
    Corrected the stale ceiling-based magnitude advice in `CLAUDE.md`
    (`AGENTS.md` is its symlink): the implemented/source rule is floor plus
    one, with a strict upper endpoint. Fresh execution of `MagSource.lean`
    passed its examples and signature checks (one existing prefer-grind
    warning). No mathematical definitions were changed by this documentation
    correction.
22. **Fixed-width comparison is executable and correctly typed:**
    `b32_compare` and `b64_compare` no longer convert to mathematical reals.
    They implement the constructor/sign/exponent/mantissa branches of the
    configured Rocq 9.2 `SpecFloat.SFcompare`, reached through pinned
    `Bits.v:676,743` and `Binary.v:773`. Their result is now `Option Ordering`,
    preserving Coq's comparison datatype rather than permitting arbitrary
    integer outcomes. There were no pre-existing callers outside the replaced
    helper definitions. Four fixed-width predecessor/successor definitions
    also compile after removing unnecessary `noncomputable` markers; their
    bodies and types are unchanged. A fresh **6,213-job** macOS build and
    changed-file LSP checks pass. The actual APIs pass **2,000** pure ordering
    laws and **200,000** native Float/Float32 comparisons; the matched pure
    Rocq ordering-law grid also passes. All **17** core harness tests pass,
    including a mutation collapsing unordered NaNs into equality. A separate
    **2,974-case** compiled/kernel/Rocq order-and-exact-unary run passed
    (seed `982731`, artifact `floatspec-bridge-lx9xecrq`), and all 2,974 generated
    kernel equalities passed in 279.573 seconds. The refreshed compiler trust
    audit checks **13,570 declarations** across all 58 source modules with only
    the same four direct/transitive manifest debts; the lexical and source-link
    regression gates also pass. The legacy generic real-valued
    `Binary.Bcompare` and primitive comparison implementations are unchanged,
    and no universal equivalence theorem connecting these implementations is
    claimed. Six more source anchors bring the registered count to **62**.

See [the three-loop guide](THREE_VERIFICATION_LOOPS.md) for commands, output
artifacts, and current coverage. Repairs include the source-link/trust gates,
the two source-facing theorem signatures above, and the value-preserving
binary-positive conversion. No rounding rule was changed to force agreement.

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
| `0fdc837d` | Defs predicates and source-anchor validation | Defs predicates match the source forms read; textual anchor bypass repaired with compiler metadata. |
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

The queued validity, duplicate-converter, and fixed-width comparison repairs
are now applied. The prior complete combined suite passed at its documented
snapshot; the new order bridge has also completed successfully. The native
arithmetic bridge still decodes through Float.Model; the new core bit families
exercise the distinct source-shaped decoder directly and retain NaN payloads.

Next execution slice: enable compiled execution of the integer-only IEEE
rounding/arithmetic path, preserving bodies and theorem types. The candidate
chain is `bsn_shr_fexp`, `binary_round_aux`, `binary_round`, the specialized
division/square-root cores, `Binary.normalize`, the six proof-carrying
arithmetic operations, and their fixed-width wrappers. Let compiler feedback
identify genuinely noncomputable dependencies; do not replace mathematical
reals by machine floats or bypass proof obligations. Extend the all-mode
bridge with compiled Lean only after the actual APIs compile. The generic
real-valued comparisons remain a separate source-contract review.

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
of that predicate. Source anchors now use compiler metadata, but the linter is opt-in,
and many public declarations are outside its current gate. Next work includes
native execution of integer-only algorithms, more IEEE arithmetic cross-tests,
and further source-signature checks. Passing compilation, finite agreement,
and a proof of a Lean statement are three different claims; none alone proves
whole-library Flocq equivalence.
