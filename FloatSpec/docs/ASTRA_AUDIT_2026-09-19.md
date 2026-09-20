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
23. **The source-shaped IEEE arithmetic itself now compiles:** twelve
    integer-rounding/core/arithmetic declarations and twelve fixed-width
    wrappers no longer carry unnecessary `noncomputable` markers. The first
    build correctly failed on `Binary.Bsqrt`'s real-valued `input` let-binding.
    That witness was only needed by the validity proof; moving it and its
    supporting proof steps inside `hvalid` removed the runtime `F2R`
    dependency without replacing real mathematics or changing the integer
    result/type. A fresh **6,215-job** macOS build passes. The actual source
    APIs pass **100,100** native Float/Float32 arithmetic comparisons (seed
    `489231`, boundary and random cases, NaNs explicitly quotiented).
    The all-mode/exact-payload bridge now runs compiled Lean as a third path.
    Source review also caught that the newly integrated runner supplied a
    `--coqc` argument missing from that bridge's CLI; the option is now
    implemented and exercised by a live compiled-only rounding mutation test.
    All **eight** bridge-harness tests pass, including both-implementation and
    compiled-only deliberate rounding mutations, all ten format/mode groups,
    strict output validation, and error handling for interruption/timeouts.
    The compiler trust audit reports **13,566 declarations**, all 58 source
    modules, and only the original four direct/transitive manifest debts.
    The fresh anchor validator checks **74** references. The reading guide's
    three-bit rounding walkthrough now executes and has closed equality
    proofs in both Lean and Rocq for all five modes and both signs.
    The later complete combined run is recorded below.
24. **The new compiled snapshot passed the complete combined suite:** seed
    `709541`, source SHA-256
    `541bfc055e147a800162233e5b08d920f28b595340f739d971caaa80993ea3c3`,
    8,684 core cases (577.203 s), 622 native unary cases (169.157 s), 1,424
    native arithmetic cases (1,154.532 s), and 590 all-mode IEEE cases
    (914.289 s). All corresponding generated kernel statements pass, as do
    all four bridges' live harness tests. The complete shell process exited
    zero. No imported product source or build output was changed mid-run.
25. **Implicit premise drift repaired in 26 public exports:** comparing
    compiled Rocq and Lean types, not just displayed theorem headers, exposed
    31 unwanted section-instance premises. The new 31 guards and six typed
    consumers all failed against the old snapshot and now pass. Corrections
    span Plus_error, Mult_error, Div_sqrt_error, Relative, and Round_odd.
    The defects predate the 23 Sol commits under review; they are not being
    attributed to that later work. A fresh 6,215-job macOS build and LSP
    diagnostics pass. The compiler trust audit reports 13,564 declarations,
    58 modules, and the same four manifest debts. No new sorry was introduced.
    The selected exports and retained source premises are listed in
    [the focused contract review](SOURCE_CONTRACT_REVIEW.md).
26. **Independent small-format arithmetic checks now go beyond agreement:**
    both assistants pass 275 exact-input, 1,055 Sterbenz, and 5,714 nearest
    addition-error representability checks. A separately enumerated rounding
    oracle checks 35,845 finite cases in all five modes. Lean proves 95
    boundary cases in the kernel; Rocq closes the full finite oracle grid.
    Deliberately forcing nearest-away instead of the requested mode fails in
    both assistants, with Lean retaining the `-13` tie as a replayable witness
    (`-14` observed versus nearest-even `-12`). These fixtures were run
    separately after the preceding aggregate receipt, not retroactively
    counted as part of it.
27. **Scale/decompose now runs in four paths:** removing four unnecessary
    `noncomputable` markers enables the integer-only `Binary.Bldexp` and
    `Binary.Bfrexp` chain without changing computation bodies or public types.
    Seed `604719` passes 2,360 exact compiled/kernel/Rocq cases and 2,360
    generated kernel regressions, with native Float/Float32 observations
    checked only in the stated mode/finite-input scope. Runtime: 408.335 s;
    source SHA-256
    `f5db09e6d0e537474ceb0d2d02e391d8646ed86e9588e43d0103728de8f790cd`.
    All seven harness tests pass, including independently mutated paths and
    error handling. The later raw-validity changes postdate this receipt.
28. **Two strong root validity statements restored:** `valid_binary_B2SF`
    now consumes the proof-carrying SingleNaN carrier and establishes actual
    canonical/bounded validity. `binary_fit_aux_correct` now exports that
    same predicate in its validity conjunct. Existing closed proofs supply
    both corrections; no new sorry is needed. Typed consumers reject the old
    weaker signatures. The full 6,215-job macOS build and LSP checks passed
    for this slice before the further raw-boundary repair below.
29. **Raw validity/conversion counterexamples found and repaired:** the new
    bridge family sends the same precision, exponent limit, sign, positive
    mantissa, and exponent through actual validators and three converter
    views. On seed `860213`, 240 of 1,180 cases disagreed before the patch;
    the same 1,180 cases now agree and yield 1,180 passing kernel regressions.
    Root `SF2B'` admitted noncanonical one `(1,0)`; `validB754` rejected
    canonical one `(4,-2)` due to its wrong mantissa bound. These defects
    predate the Sol audit range. The paired fixture preserves the witnesses,
    and the raw/proof-carrying converter equality is proved for all inputs.
    Adding the source link also exposed the anchor validator's mishandling
    of apostrophes in Coq names: its new failing test now passes after the
    identifier-boundary correction.
    The repaired validity grid took 80.249 s at source SHA-256
    `98afa4bd627ef35e5aa492f714004382e19d63bd2ad803205e5650ebcb1b2790`.
    Nineteen core-bridge tests, seven scale-harness tests, and three source-link
    tests pass, including live deliberate mismatches. Fresh compiler metadata
    validates 105 anchors; the trust audit still reports 13,564 source
    declarations in 58 modules with exactly four manifest debts. The later
    complete 6,215-job macOS build also includes comment-only corrections to
    outdated ceiling-of-log descriptions in Raux.

See [the three-loop guide](THREE_VERIFICATION_LOOPS.md) for commands, output
artifacts, and current coverage. Repairs include the source-link/trust gates,
the two source-facing theorem signatures above, and the value-preserving
binary-positive conversion. No rounding rule was changed to force agreement.

### Expanded frozen-snapshot receipt

The complete five-bridge suite at `ba3e2a8b` exited zero on 19 September,
23:45 UTC. Seed `961703`, source SHA-256
`b736791a1fa66312a60c3e033108120dfbbd65c1914fb68674773b56bbdc7cc4`:

| Bridge | Cases and generated kernel regressions | Seconds |
|---|---:|---:|
| Core, 19 families | 10,788 | 729.964 |
| Native unary | 672 | 184.428 |
| Native arithmetic | 1,624 | 1,305.483 |
| IEEE all-mode arithmetic | 690 | 1,083.949 |
| Scale/decomposition | 2,560 | 438.611 |

All independent Lean/Rocq fixtures and all 48 live bridge harness tests also
pass. Native comparisons retain their documented domain/mode restrictions.
The imported Lean sources, harnesses, and build outputs stayed fixed throughout
the run; only audit prose and out-of-tree diagnostic probes changed. This
receipt must not be relabeled as verification of subsequent source repairs.

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

### Integer slice prepared during the completed aggregate run

The committed `ba3e2a8b` sources stayed fixed during the expanded aggregate
run (seed `961703`), which has now completed successfully as recorded above.
The following probes were prepared out of tree while that run was active.

Separate temporary probes have identified the next source-facing slice:

- At `ba3e2a8b`, `Binary.Btrunc` and `BinarySingleNaN.Btrunc` defined the operation
  through noncomputable real-valued `Ztrunc`. Pinned SingleNaN source line
  2680 supplies an integer algorithm. An out-of-tree replacement follows that
  algorithm and has a closed correctness proof under the source
  `Prec_lt_emax` premise. That initial probe did not change the public APIs;
  the integrated result is recorded below.
- The compiled Rocq type of `Binary.Bnearbyint` requires `Prec_lt_emax`, but
  not `Prec_gt_0`; the Lean export then asked for both. A computable
  out-of-tree implementation with the smaller source premise is
  definitionally equal to the existing body when the latter is applicable.
- An exploratory 3,020-case test of the actual `SFnearbyint_binary_aux` and
  `SFnearbyint_binary` functions agrees in compiled Lean, kernel reduction,
  and Rocq, including raw out-of-format inputs. All 3,020 generated kernel
  equalities pass. Artifact: `/private/tmp/floatspec-nearby-audit-20260919`.
- The replacement prototype passes 1,560 bit-level cases in compiled Lean,
  kernel reduction, and Rocq, with scoped native rounding/conversion checks.
  This first receipt tests temporary definitions, not the then-unchanged public
  `Btrunc` APIs. Artifact:
  `/private/tmp/floatspec-integer-prototype-wrapped-parser-20260919`.
- Independent eighth-integer selection and idempotence tests cover 5,125
  cases in each assistant; Lean additionally checks the whole grid in its
  kernel. That first Lean test used the temporary replacement; Rocq used
  actual pinned definitions. Permanent public-API fixtures now replace that
  prototype-only evidence, as recorded below.
  Deliberately replacing every requested mode with nearest-away is rejected
  by the Rocq theorem and Lean runtime oracle; the latter reports the concrete
  nearest-even counterexample `-500/8`. Lean's kernel rejects that same
  individual counterexample. A whole-grid negative diagnostic was terminated
  after excessive evaluation time and remains an error; only the bounded
  counterexample is counted as a successful kernel mutation test.
- A separate 952-case probe of actual generic SingleNaN successor,
  predecessor, and ULP definitions agrees in Lean kernel reduction and Rocq.
  It covers precisions 1, 2, 3, 4, 24, and 53, exceptional constructors,
  normal/subnormal/overflow boundaries, and rejected raw representations.
  No compiled path is claimed: these public implementations still carry
  `noncomputable` markers. Artifact:
  `/private/tmp/floatspec-neighbors-kernel-audit-20260919`.
- Large binary64 truncation results exposed two harness limits: the default
  kernel exponentiation threshold and a parser that accepts only a literal
  space after `Int.ofNat` / `Int.negSucc`. Lean legitimately wraps very long
  integers onto the next line. The failed prototype runs remain errors; the
  successful probe used an explicit threshold and a temporary whitespace
  parser correction. The shared parser repair is now committed in `0091e3d0`.

The noncomputable truncation definitions originate in `3d6126a8`, an ancestor
of upstream `158263e9`; they are not a regression introduced by the 23 Sol
commits. No new proof debt is introduced by the replacement.

### Integrated public integer APIs

The source algorithm now backs `Binary.BtruncSingle`, `Binary.Btrunc`, and
`BinarySingleNaN.Btrunc`. Their real-value theorems are closed under exactly
the source `Prec_lt_emax` premise. Both nearby-integer interfaces execute;
the Binary definition and theorem no longer demand an extra `Prec_gt_0`.
Six new elaborated-type guards and typed Lean/Rocq consumers preserve that
boundary, including a zero-precision SingleNaN control. No new sorry is used.

At source SHA-256
`7376fd07802fed79f3ba80e291e0e2d347979cf18d751867f44465380ff3c363`:

- The permanent public-API integer bridge passes **1,460 cases and 1,460
  kernel regressions**, seed `730519`, 220.468 seconds. Exact compiled Lean,
  kernel, and Rocq results agree; native checks have explicit mode/range limits.
  Artifact: `/private/tmp/floatspec-integer-public-20260919`.
- The new twentieth core family passes **3,120 raw-helper cases and kernel
  regressions**, seed `813047`, 223.6 seconds, including invalid later-theorem
  precision/exponent domains. Artifact:
  `/private/tmp/floatspec-nearby-public-20260919`.
- Both permanent independent oracles pass **5,125** eighth-integer selection
  and idempotence cases; Lean closes the whole finite grid in its kernel.
- All eight integer-harness tests pass, including wrong-mode mutations in
  the independent kernel/runtime/Rocq oracles and in each differential path.
- The complete macOS Lean 4.34 build passes (6,215 jobs), and all three changed
  definition/contract files have fresh complete LSP diagnostics with no errors.
- All 24 core-harness tests pass. Fresh compiler metadata validates 118 pinned
  source anchors; the compiled trust audit covers 13,573 source declarations in
  58 modules and reports only the same four manifest-recorded proof debts.

Integration initially exposed two shadowed alignment helper names (Nat versus
positive carrier); explicit root qualification resolved the compiler errors.
A first Rocq fixture invocation used an incompatible output basename and
failed; the corrected invocation passes. These failures are not counted as
successful runs. The shared helper/proofs and source-facing wrappers are now
tested as public definitions, not silently substituted prototype expressions.

Further inspection of the first two broad Sol commits compared all their
changed mathematical surfaces: the three-field `satisfies_any` contract,
signed integer powers, format predicates, FullFloat finite/NaN validity,
source-link metadata, and explicit native proof debts. These comparisons do
not certify every unchanged theorem in the affected modules. A separate
324-case kernel/Rocq grid of actual `Pff2FlocqAux.make_bound` covers radices
2, 3, and 10, precisions -3 through 8, and both signs of exponent bounds.
It agrees with pinned Rocq, including negative-power conversion through
`Z.to_pos`; compiled execution is not claimed. The Rocq-compiled
`make_bound_Emin` signature confirms that only the nonpositive exponent-bound
premise is needed, while `make_bound_p` retains positive precision.
Receipts: `/private/tmp/PffBoundsProbe.lean`, `/private/tmp/PffBoundsProbe.v`,
and `/private/tmp/PffBoundsProbe.receipt.json`.

The former legacy `valid_binary_SF := true` was also reproduced as an
executable discrepancy: precision 3, maximum exponent 4, positive mantissa 1,
exponent 0 returns `true`, while both the repaired source-shaped predicate and
Rocq return `false`. The issue is already disclosed above, but these probes
confirm its exact observable behavior. Its two experimental payload theorems
have no callers elsewhere in this repository; repairing their input validity premises
would allow the vacuous definition to be removed without admitting proofs.
Probe files: `/private/tmp/LegacyValidityProbe.lean` and `.v`.
`git show 158263e9:FloatSpec/src/IEEE754/Binary.lean` confirms the same
always-true definition at upstream; its introduction is `e9746f40` from
October 2025, not one of the 23 later Sol audit commits.

That predicate is now repaired, including positive mantissa, canonicality,
and upper exponent checks. The two experimental payload adapter contracts
require actual input validity. The full build exposed two further `by rfl`
validity arguments inside a downstream addition proof; they now consume
`binary_round_correct`'s real validity conjunct via a closed predicate-equality
lemma. Initial failed builds (missing validity, then predicate unfolding) are
not passes. The final full `lake build` passes (3,101 jobs), and fresh complete
LSP diagnostics for both edited modules report no errors. No proof debt was added.

The original five-case red corpus had three mismatches, retained at
`/private/tmp/floatspec-legacy-validity-before-20260919`. Replaying all five
after the repair passes compiled Lean, kernel reduction, Rocq, and generated
kernel regressions (`/private/tmp/floatspec-legacy-validity-after-20260920`).
An expanded 1,280-case grid (seed `294883`, 89.785 seconds) also passes all
paths and all 1,280 bootstrapped proofs at source SHA-256
`2b22892ed1bd50a27e2914b7b9c11fe7cb82bcec81821f9f6164640dac061a4e`.
Artifact: `/private/tmp/floatspec-validity-public-20260920`.
The permanent pure Lean fixture proves the two validity names agree for every
local constructor and parameter choice, and rejects zero mantissas which the
source positive carrier cannot represent.
All 25 core harness tests pass, including a live mutation restoring the
always-true result; both Lean execution paths reject that mutation against Rocq.

The subprocess cancellation defect is now repaired: on macOS/Linux the runner
owns a process group and kills/reaps it on timeout or interruption, rather than
leaving a prover child alive. The scoped `/private/tmp/FloatSpecTimeoutProbe.py`
reproduced the old failure and cleaned up its own child. The permanent sentinel-
writing descendant test fails before the change and passes afterwards, alongside
success, nonzero-exit, strict-stderr, and interruption controls. The shared
integer parser also now accepts legitimate whitespace after `Int.ofNat` and
`Int.negSucc`; a permanent 309-digit maximum-binary64 regression reproduces its
old failure. All 23 core harness tests pass after integration (49.813 seconds).
The other four bridge harnesses also pass: 7 unary, 7 arithmetic, 8 all-mode,
and 7 scale tests, for 52 harness tests altogether after this change. The
complete cached macOS Lean build also passes (6,215 jobs); no product Lean source changed in this
tooling slice. Existing timeout/error records remain errors, not relabeled passes.

The queued validity, duplicate-converter, and fixed-width comparison repairs
are now applied. The prior complete combined suite passed at its documented
snapshot; the new order bridge has also completed successfully. The native
arithmetic bridge still decodes through Float.Model; the new core bit families
exercise the distinct source-shaped decoder directly and retain NaN payloads.

The integer-only IEEE arithmetic and scale/decompose chains, compiled bridges,
two root validity exports, and raw validation/conversion repairs are now
implemented with the slice-specific receipts above. The expanded aggregate
has now verified all those later fixtures and scale/validity additions at
`ba3e2a8b`; it predates the now separately verified public integer-truncation
slice and the now separately verified legacy validity repair. Generic real-valued
comparisons and further theorem-contract audits remain separate slices.
Do not replace mathematical reals with machine floats or bypass proof
obligations merely to make a declaration compile.

Maintain three separate loops: independent Lean tests, independent pinned
Flocq/Rocq tests, and a differential bridge that sends identical inputs to both.
Record concrete cases and seeds; promote disagreements to permanent regression
examples. Keep valid theorem domains distinct from total-function behavior
outside those domains. Test the bridge with intentional mismatches so a parser
or skipped command cannot silently produce a green result.

## Generic neighbors: executable source algorithms

Eight integer-only SingleNaN/full-payload successor, predecessor, and ulp
declarations now compile without `noncomputable`; their bodies and types are
unchanged. Source branches were read against SingleNaN lines 3099, 3242,
3412 and Binary lines 1368, 1392, 1421. The twenty-first core family observes
validity, conversion, successor, predecessor, and ulp in generic formats.
The fixed-width order families additionally execute the generic full-payload
algorithms, independently of the existing bit-level neighbor implementations.

At source SHA-256
`8b72c2224acb46bd7fcaf2bac6fc132bb4bba8e956001351ec3ee1d9eee6de8d`,
**2,510 differential rows and all 2,510 generated kernel regressions pass**
(seed `681943`, 289.349 seconds): 687 binary32 rows, 687 binary64 rows, and
1,136 generic SingleNaN rows. Artifact:
`/private/tmp/floatspec-neighbors-public-20260920`.
The pure Lean ordering grid now checks generic/bit-level agreement too;
the paired Lean and Rocq fixtures retain explicit signed-zero, max-finite,
and NaN-payload boundaries. All 27 core harness tests pass, including a
deliberate successor-to-predecessor mutation. Complete fresh diagnostics
for the two implementation files and the ordering test contain no errors.
The compiled source validator checks 126 pinned anchors. The fresh compiled
trust audit covers 13,574 source declarations across 58 modules and finds
only the four existing manifest debts. No new proof debt is introduced.
Finite agreement is not a universal source-equivalence proof.

## Contract corrections developed during the frozen aggregate

The aggregate begun at 00:24 UTC on September 20 freezes the implementation
and harness at `957b5f40`. That checkout remains unchanged until the run
finishes, so each result has an unambiguous source snapshot. Corrections were
developed and verified in an isolated managed worktree with its own cloned
build artifacts; no build output was shared with the running aggregate.

The following discrepancies were reproduced before repair:

- Full-payload `Binary.Bcompare` returns `Option Int`, while pinned
  `Binary.v:773` returns `option comparison`. A Rocq consumer demanding
  `option comparison` compiles, while its Lean `Option Ordering` counterpart
  fails with a type mismatch. The SingleNaN façade has the correct result type
  already; both generic comparisons used non-executable real comparison.
  The distinct fixed-width comparisons are executable and covered by the
  permanent bridge. Probe files: `/private/tmp/GenericComparisonContract.lean`
  and `/private/tmp/GenericComparisonContract.v`. An isolated executable
  integer implementation now has closed SingleNaN/full-payload correctness
  and reversal proofs, without precision instances or new axioms:
  `/private/tmp/GenericComparisonRepair.lean`. These are draft results until
  the actual public endpoints and their consumers are rebuilt and exercised.
- `Generic_fmt.lt_cexp_pos` and `lt_cexp` demand `Valid_exp fexp`, but their
  pinned exports (lines 1583 and 1596) need only `Monotone_exp fexp`.
  Paired consumers reproduce the extra Lean premise. An isolated closed proof
  compiles without validity, including a consumer with the monotone, invalid
  exponent function `e ↦ e + 1`; its reported axioms are only `propext`,
  `Classical.choice`, and `Quot.sound`. Typed pinned-Rocq consumers also
  confirm the adjacent `cexp_le_bpow` and `cexp_ge_bpow` exports omit
  validity; all four Lean exports added it unnecessarily.
  Probe files: `/private/tmp/CanonicalExponentContract.lean`,
  `/private/tmp/CanonicalExponentContract.v`, and
  `/private/tmp/CanonicalExponentRepair.lean`.
- Five Raux source theorem names (`Rcompare_Lt`, `Rcompare_Eq`, `Rcompare_Gt`,
  `Rcompare_not_Lt`, `Rcompare_not_Gt`) denoted integer-returning
  wrappers instead of propositions. Their comment explicitly says they were
  introduced for documentation cross-references. All five typed Lean
  consumers fail, while the paired source consumers compile against Raux
  lines 371, 411, 428, 392, and 449. Closed replacement propositions compile
  in `/private/tmp/RealComparisonContracts.lean`. This correction alone does
  not migrate the broader Raux `Rcompare` API from integer codes to
  `Ordering`; that representation boundary must remain explicit. Failure
  probes: `/private/tmp/RealComparisonCurrent.lean` and `.v`.

An isolated small-format arithmetic run completed all 6,160 shared inputs
at precisions 2, 3, 4, and 8, two exponent ranges per precision, all five
rounding modes, and six arithmetic operations per row. It compares actual
compiled full-payload Lean operations (with a fixed valid NaN handler), Lean
kernel reduction, and pinned Rocq SingleNaN operations. Payloads are erased
deliberately in this probe, not claimed tested by it. Every boundary pair is
included; FMA's third operand is rotated rather than exhaustive. The driver
is `/private/tmp/floatspec-small-format-audit.py`; this is not yet a permanent
repository test. All 6,160 rows agreed and all 6,160 generated kernel
regressions checked (seed `491731`, 1,463.536 seconds), at the frozen source
SHA-256 `8b72c2224acb46bd7fcaf2bac6fc132bb4bba8e956001351ec3ee1d9eee6de8d`.
Artifacts: `/private/tmp/floatspec-small-format-arithmetic-20260920`.
Driver SHA-256: `387bf90fa552eecc3e8c891938cefd48861b14710fa3d168550f1d491030ec4d`.

The isolated comparison draft also passed 1,518 shared rows and all 1,518
generated kernel regressions (seed `668013`, 147.877 seconds), including
negative/zero precision, precision equal to the exponent bound, exceptional
values, and malformed finite representations. Artifacts:
`/private/tmp/floatspec-comparison-draft-qualified-20260920`.
Because its implementation is embedded from a draft outside the repository,
the repository fingerprint alone does not identify this experiment. The
draft implementation SHA-256 is
`595c3f24fc5a7744ea1b89960bd2a813cea5580f7b27b069f56471ba5419b962`;
driver `/private/tmp/floatspec-comparison-audit.py` has SHA-256
`8ae4335451c3b89210ae35aed526b72a618ba765640d8655e5f9944c30d70398`.
Generated programs retain the embedded implementation. The first draft run
failed because an opened Bracket namespace made `compare` ambiguous; explicit
`Ord.compare` fixed that elaboration failure before the passing run. Fresh
axiom reports for both correctness and reversal theorems contain no `sorryAx`.

Two verified integration commits now repair these discrepancies:

- `2eb81443` removes the four extra canonical-exponent validity premises and
  restores the five Raux comparison propositions. Full macOS Lean 4.34.0
  build: 6,215 jobs; paired Rocq consumers and previously failing Lean
  consumers now pass. The invalid monotone exponent control is proved invalid,
  rather than merely described that way. The source SHA-256 is
  `f090bf1b61a88787880f7f091255bc7307fa803b0c2d645edadaa18587d1bcd1`.
- `ec3b630f` restores executable `Option Ordering` at both generic public IEEE
  comparison endpoints, with closed value/reversal proofs and no new precision
  premises. Binary32/64 comparison delegates to that same proved primitive,
  so these Lean endpoints are not independent implementations. Pinned Rocq
  and native Float/Float32 remain independent checks. Seed `668019` passes
  3,567 shared cases and all 3,567 kernel regressions in 359.999 seconds;
  all 29 core harness tests pass, including operand-swap mutations.
  Artifact: `/private/tmp/floatspec-comparison-public-20260920`.
  Full build: 6,215 jobs; complete LSP error diagnostics are clean in the
  five changed implementation/contract test modules. Paired Rocq consumers
  and the independent ordering fixture compile. Source SHA-256:
  `ef0fbd7b679679ce0bccc073d2b732fd31741f101f7067887c3b4b69e10fbb1a`.

The latter compiled trust audit checks 13,591 source declarations in 58 modules,
with four unchanged manifest debts, no new project axioms, and no runtime
overrides. Source metadata validates 142 pinned anchors; the premise regression
has 45 source guards. The initial Rocq output-basename and explicit-argument
setup errors were corrected before the passing consumers and are not semantic
counterexamples. Logs for both integration commits are retained in both
worktrees. These slice results are separate from the frozen aggregate below.

## Final verification and handoff

### Complete frozen aggregate

The complete six-bridge runner exited **0 at 01:53 UTC on 20 September**,
after running continuously against commit `957b5f40` and source SHA-256
`8b72c2224acb46bd7fcaf2bac6fc132bb4bba8e956001351ec3ee1d9eee6de8d`.
Its source/build directory was not changed during the run; later repairs
used a separate worktree with independent APFS-copied build artifacts.

| Differential slice | Shared cases | Kernel regressions |
|---|---:|---:|
| Core and generic IEEE boundary families | 15,036 | 15,036 |
| Native binary64 unary / decomposition / neighbors | 672 | 672 |
| Native arithmetic pairs | 1,624 | 1,624 |
| Binary32/64 rounding modes and payloads | 690 | 690 |
| Scale/decomposition | 2,560 | 2,560 |
| Integer rounding | 1,660 | 1,660 |
| Total rows across the six bridges | **22,242** | **22,242** |

All 64 bridge-harness tests passed (27 + 7 + 7 + 8 + 7 + 8), including
deliberate semantic mutations, malformed/truncated output, source drift,
timeouts, and interruption. Independent pure Lean and pure Rocq suites also
passed, including 10,734 arithmetic invariant cases each, 20,000 bit
roundtrips, 35,845 independent rounding-selection cases each, and 5,125
integer-rounding oracle cases each. The aggregate additionally executes
100,100 native arithmetic comparisons. These categories overlap and must
not be summed into a claimed count of distinct floating-point inputs.

The exact command, progress, and report-directory paths are in
`/private/tmp/floatspec-complete-three-loops-20260920.log`. Seed `741193`
was used throughout, with sample sizes 150 core, 250 native unary,
150 arithmetic, and 40 each for modes/scaling/integer rounding.
This is a successful **finite** aggregate on the frozen snapshot, not
universal source equivalence and not an aggregate run of later changes.
The newer comparison and small-format families have separate passing runs
below; the final source also receives a cross-family replay and full harness
rerun.

### Persistent small-format bridge and last contract repair

Commit `4183a790` adds the twenty-third core bridge family, `small_ieee`.
Seed `491733`, ten supplemental cases per format/mode, passed all 6,160
shared-input cases and 6,160 Lean kernel regressions in 911.384 seconds.
The 32-test core harness passed in 87.006 seconds, including deliberately
changing addition into subtraction and rejecting it in both Lean paths.
Artifact: `/private/tmp/floatspec-small-format-permanent-20260920`.
This run used source SHA-256
`ef0fbd7b679679ce0bccc073d2b732fd31741f101f7067887c3b4b69e10fbb1a`.

Commit `0f3f2550` restores `Raux.Rcompare_IZR` as an actual proposition,
retaining its old carrier under the explicit `_check` compatibility name.
The previously failing Lean client and paired Rocq consumer now compile.
Its proof is closed; it adds no proof debt. Full library build: 3,101 jobs;
test/executable build: 6,215 jobs. Complete LSP error diagnostics are clean
for Raux and the premise test. The compiled audit checks 13,591 declarations
in 58 modules and the same four debts; 143 source anchors validate.

One source-validator invocation overlapped the first build and failed with
an artifact-write permission error in `Pff2Flocq.ilean`. It is recorded as a
failed invocation, not a successful gate. After the initial build completed,
the sequential regression build, source validator, compiled trust audit,
scanner/linter regressions, unused-mvcgen check, and proof-debt check all
exited successfully. Logs: `/private/tmp/floatspec-izr-final-build-20260920.log`
and `/private/tmp/floatspec-izr-final-regressions-20260920.log`.

A final-source replay selects the first, middle, and last case from each of
23 families in the corpus generated with seed `903117` and three supplemental
samples. All 69 shared cases and 69 kernel regressions passed in 17.636
seconds. This is a small integration check, not a rerun of every large corpus.
Its replay JSON is `/private/tmp/floatspec-final-replay-20260920.json`, report
directory `/private/tmp/floatspec-final-source-replay-20260920`, and source
SHA-256 `1d72b9702518a1ac333eb7ba568f6d0be3775dc70b9d22f3f51d00998c63071d`.
The report's default seed field is unused for replay; the input JSON is the
authority for this run.

The final-source rerun of all six bridge harnesses also exited 0: **69 tests**
(32 + 7 + 7 + 8 + 7 + 8), with the live pinned reference enabled. Respective
suite times were 84.914, 12.967, 19.087, 24.734, 25.253, and 31.965 seconds.
These include actual Lean/Rocq/native invocations and deliberate mutations,
not merely parser-unit tests. The implementation snapshot was unchanged
throughout this rerun.

### Final original-checkout build and artifact-cache correction

After the frozen aggregate exited, the original branch fast-forwarded to the
verified integration commits without changing `Deps/flocq`. A plain Lake build
reported success, but immediately executing the demo failed: the user's global
`LAKE_ARTIFACT_CACHE=true` allowed cached imports to remain outside the usual
`.lake/build` paths. Missing `Bits.olean`, `Raux.olean`, and `FloatSpec.olean`
were directly observed. That build-only result is not a working-checkout pass.

A sequential build with artifact caching disabled for that command rebuilt
the affected modules and passed all 6,215 jobs. The project now sets
`restoreAllArtifacts := true`, the Lake 4.34 package option documented in
`Lake/Config/PackageConfig.lean`, so external fixture consumers receive local
imports even with the global cache still enabled. No user environment setting
was changed. With the ordinary environment restored, a further 6,215-job
build, the actual five-part demo, the integer-comparison consumer, compiled
trust audit, and all 69 replay cases/kernel assertions passed. The lakefile's
complete LSP error diagnostics are clean. This build-configuration repair
does not change any mathematical definition or theorem statement.

The rebuild log is
`/private/tmp/floatspec-final-materialized-macos-build-20260920.log`; the final
replay report is `/private/tmp/floatspec-final-materialized-replay-20260920/report.json`.
This last replay records the new configuration fingerprint separately from
the earlier implementation-only verification receipts: all 69 cases passed
in 17.767 seconds with SHA-256
`a582d3e7d26c8a2df150424f298b5bb0e4c0e71a61b9c7a958b0713ab300aa10`.

### Reviewable fork and executable introduction

The user authorized creating `alok/FloatSpec` after the BAIF push returned
403. The fork exists, and verified integration commits are pushed to
`origin/codex/astra-flocq-audit`. `origin`, `remote.pushDefault`, the branch's
tracking remote, and the GitHub CLI default now use the user's fork. BAIF
remains named `upstream`; no history was force-pushed and no account changed.

Fork CI is **not green**: runs `35482067588` and `35482293729` fail in the
Lean action's automatic mathlib-cache step, before project compilation.
The cache refuses the project toolchain `4.34.0` because the retained mathlib
pin declares `4.34.0-rc2`. This is not a Lean source diagnostic or a passing
Linux build. The proposed narrow fix is disabling that incompatible cache
and building the reviewed dependency sources; user approval was requested
under the CI skill's approval rule. No dependency or toolchain pins were
changed to conceal the mismatch.

The five-part `scripts/fixtures/GuidedDemo.lean` executes exact addition,
all rounding modes, double rounding, signed zero/NaN ordering, and canonical
raw validity. Every example has a closed kernel assertion plus a compiled
runtime check. It ran successfully and is included in CI and the aggregate
runner. The linear guide links to `DEMO_EXEMPLARS.md`, which explains the
code-reading route and records precisely which external examples were read
versus built. Pinned Flocq `Compute.v` and `Average.v` both compiled with
Rocq 9.2 (deprecation warnings only). FloatLib's presentation was inspected,
not built or certified here.

### Independent pinned Rocq proof-object check

Rocq 9.2's standalone checker completed successfully over every built source
module and its recursive dependencies:

```sh
rg --files src -g '*.v' | sed 's#^src/#Flocq/#; s#\.v$##; s#/#.#g' |
  xargs /opt/homebrew/bin/coqchk -silent -o -Q src Flocq
```

This ran in `/private/tmp/flocq-audit-pinned-7aab8f55`, with no `-admit` or
`-norec` option. The checkout remained clean at the pinned commit. Its 34
tracked `.v` files plus generated `Version.v` give 35 built modules, all
matched to existing Lean files (Core/Core maps to the Core umbrella).
The reading guide's older count of 36 is corrected, not turned into a
completion percentage. Log:
`/private/tmp/floatspec-pinned-rocq-kernel-check-20260920.log`.

The context report lists classical real/function-extensionality assumptions
and standard Rocq primitive integer/float axioms; it does not claim native
hardware is proved axiom-free. It reports no type-in-type, unsafe (co)fixpoint,
or assumed-positivity dependencies. This is reference proof-object checking,
not a proof that the Lean port is equivalent to that reference.

### Remaining adjacent API gaps reproduced

The integer-cast comparison mismatch was reproduced before the repair above:
`/private/tmp/RcompareIZRContract.lean` failed with `Int` versus `Prop` while
the paired Rocq consumer passed. The same Lean client passes after `0f3f2550`.

`BinarySingleNaN.Beqb`, `Bltb`, and `Bleb` still use real-valued decisions.
`/private/tmp/BooleanComparisonExecutionGap.lean` confirms even a compiled
signed-zero equality client fails on `noncomputable`. Their inspected finite
correctness statements agree with the source Boolean contracts, but the new
executable `Bcompare` does not by itself make those separate APIs executable.
This is an execution gap, not a demonstrated incorrect Boolean result.

### Unreviewed scope

The bulk of the complete theorem-by-theorem port remains unreviewed. In
particular, repairing `valid_binary_SF` and its consumers does not certify
every legacy compatibility theorem or experimental carrier. Source anchors
now use compiler metadata, but the linter is opt-in,
and many public declarations are outside its current gate. Next work includes
native execution of integer-only algorithms, more IEEE arithmetic cross-tests,
and further source-signature checks. Passing compilation, finite agreement,
and a proof of a Lean statement are three different claims; none alone proves
whole-library Flocq equivalence.
