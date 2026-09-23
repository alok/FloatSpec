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

At the end of the September 19 block, `BinarySingleNaN.Beqb`, `Bltb`, and
`Bleb` still used real-valued decisions.
`/private/tmp/BooleanComparisonExecutionGap.lean` confirms even a compiled
signed-zero equality client fails on `noncomputable`. Their inspected finite
correctness statements agree with the source Boolean contracts, but the new
executable `Bcompare` does not by itself make those separate APIs executable.
This is an execution gap, not a demonstrated incorrect Boolean result.

### September 20 continuation: executable Boolean comparison

The continuation beginning 06:13 UTC fixes that reproduced execution gap.
`Beqb`, `Bltb`, and `Bleb` now inspect the source-shaped integer comparator.
The root definitions and namespace aliases retain their public types, and
the three finite correctness theorems plus NaN-aware reflexivity remain closed.
Their axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` was introduced. Six new source links refer to the
exact pinned Boolean exports. Pinned `Binary.v` has no corresponding Boolean
trio, so no full-payload exports were invented.

Verification on the unchanged implementation snapshot:

- Full macOS Lean 4.34.0 library/test/executable build: **6,216 jobs**, exit 0.
  Log: `/private/tmp/floatspec-boolean-full-build-20260920.log`.
- Complete LSP error diagnostics: clean for BinarySingleNaN, BitOrderExecution,
  BooleanComparison, and GuidedDemo. One earlier editor probe retained a stale
  imported `.olean` and reported the old noncomputable declaration; the fresh
  CLI fixture and subsequent diagnostics passed after the module build.
- Eight literal boundary expectations execute independently in the paired
  `BooleanComparison.lean` / `.v` fixtures. Lean additionally kernel-checks
  the table. The first Rocq fixture invocation omitted `@` on implicit source
  arguments and failed elaboration; the corrected invocation passed.
- **4,210** shared-input comparison cases, seed **702061**, 300 supplemental
  samples per each of ten formats, **14 columns** each: compiled Lean,
  kernel reduction, and pinned Rocq agree. All **4,210** generated Lean
  assertions also pass. Source SHA-256:
  `53593e9a2aedc6a490a35f735d00a35033837eaaa9eae3bbe1384c7a9f620212`.
  Report and replayable inputs:
  `/private/tmp/floatspec-boolean-comparison-20260920/` (312.467 seconds).
- **34** live core harness tests pass in 105.106 seconds, including NaN
  equality and strict/non-strict comparison mutations rejected in both Lean
  paths. Log: `/private/tmp/floatspec-boolean-harness-20260920.log`.
- The standalone ordering loop passes its existing 200,000 native order
  comparisons plus **600,000 native Boolean comparisons** of the three
  public APIs; seed **388312**. Native agreement is finite runtime evidence,
  not a proof of the primitive implementations.
- The updated five-part demo runs successfully. The compiled trust audit
  checks **13,594 declarations in 58 modules**, with exactly the same four
  named debts and no project axioms, runtime overrides, or unexpected axiom
  dependencies. **149** compiled source anchors validate. The generated
  status is unchanged. A mistyped audit-script path and an unsupported
  status-script flag were failed setup invocations, not passing checks.

The linear guide now starts with a maintained wake-up summary. It explains
the difference between a correct noncomputable specification and an executable
implementation, gives the four-outcome Boolean table, and keeps CI and proof
boundaries visible.

The next contract mismatch was independently reproduced without editing the
running test snapshot: `Binary.B2R_inj` and `Binary.B2R_Bsign_inj` require
`Prec_gt_0` and `Prec_lt_emax` in Lean, but neither premise occurs in the
compiled pinned Rocq types. `/private/tmp/IEEEInjectionContract.lean` fails to
synthesize `Prec_gt_0`; the Rocq inspection client succeeds. The SingleNaN
counterparts already omit both. This finding remains pending correction at
this milestone.

### September 20 continuation: full-payload injectivity premises

The next slice corrects the just-recorded mismatch in `Binary.B2R_inj`,
`Binary.B2R_Bsign_inj`, and `Binary.canonical_canonical_mantissa` against
pinned `Binary.v:392,473,321`. The root injectivity implementation and its
canonical-mantissa compatibility helper are corrected alongside them. The
helper's unused section instances were the reason a simple removal at the
public theorem initially failed. Omitting them lets all existing proof
bodies close without new assumptions or sorries. Finite-strictness and sign
equality are retained exactly where the source requires them.

Five new compiler guards bring the total to **50**, and three paired typed
Lean/Rocq consumers compile without either precision premise. The original
`/private/tmp/IEEEInjectionContract.lean` failing client now compiles. All five
affected proof axiom reports contain only standard Lean/mathlib axioms.
Full macOS Lean 4.34.0 build: **6,216 jobs**, exit 0; log:
`/private/tmp/floatspec-injection-full-build-20260920.log`. Complete LSP error
diagnostics are clean for Binary, BinarySingleNaN, and SourcePremiseContracts.
The initial canonical consumer draft used the internal FLT exponent arguments
in source order and correctly failed; the test was corrected, not the API.

The changed slice alters theorem interfaces, not runtime algorithms. A small
integration replay across all 23 families passed **69 shared cases and 69
kernel assertions**, not a repeat of the earlier full comparison corpus.
Report: `/private/tmp/floatspec-injection-replay-20260920/report.json`, elapsed
17.192 seconds; exact inputs are in its `cases.json` (the report seed is unused
when replaying). Source SHA-256:
`a88f1b225dfea923c5062755bdd748877938682ff7f47a6254631506062e23f2`.
The trust audit remains **13,594 declarations / 58 modules / four named
debts**; **153** source anchors validate. The generated status is unchanged.

Next inspected execution gaps are in the separate SingleNaN arithmetic exports
and source-shaped rounding wrappers, which still carry `noncomputable`
markers. Pinned full-payload `binary_round_aux` and `binary_round` also have no
precision premises, unlike their current Lean wrappers. These are candidates
for the next explicitly tested slice, not completed repairs in this receipt.

### September 20 continuation: executable raw rounding exposes a signed-shift bug

The full-payload `Binary.binary_round_aux` and `Binary.binary_round` wrappers
no longer require `Prec_gt_0` / `Prec_lt_emax`, absent from the compiled pinned
types at `Binary.v:893,991`. Those wrappers and their SingleNaN counterparts
now execute without `noncomputable`; their wrapping bodies are unchanged.
Four source anchors and two compiler guards bring the totals to 157 and 52.
Paired typed consumers compile with arbitrary integer format parameters.

The new `ieee_round` bridge family compares both raw operations through both
carriers, retaining 16 output columns. Nine formats include ordinary binary32
and binary64, small formats, nonpositive precision, and `emax <= prec`.
Auxiliary mantissas are signed; `binary_round` retains the source's positive
carrier. Modes, signs, discarded-part locations, boundaries, and seeded
supplemental inputs are all explicit.

**Actual semantic finding:** seed 826411, 150 supplemental samples per format,
found **197 disagreements in 6,354 inputs**. Every difference involved a
negative auxiliary mantissa; no nonnegative auxiliary or positive-input
`binary_round` result differed in that run. The report remains a failure:
`/private/tmp/floatspec-raw-round-v2-20260920/report.json`, 430.863 seconds,
source SHA-256
`9b6e210b8a5931d53334e47e2d7d52ad97095d179af4a431a243181fe5551e33`.
Its 4,054 kernel assertions came only from agreeing batches and must not be
reported as a successful overall run.

For `(prec, emax, mode, sign, mantissa, exponent, location) =
(3, 4, RNA, true, -7, -6, exact)`, Lean returned NaN and Rocq returned negative
zero. There were also finite and infinite reference results among the
disagreements. `bsn_shr_fexp` used Calc's Euclidean-division truncation for
every signed mantissa. Pinned `SpecFloat.shr_fexp` instead uses the signed
`shr`/`shr_1` algorithm, which truncates toward zero. Flocq's
`BinarySingleNaN.v:1072 shr_fexp_truncate` explicitly requires `0 <= m`.
The shortcut already existed in upstream `158263e9`; it was not introduced
by the earlier 23-commit audit.

**Correction:** use the existing truncation implementation when `0 <= m`,
and the actual signed shift otherwise. The private shortcut-equality lemma
now states its missing nonnegativity condition. A new closed Lean lemma
connects the combined implementation to the source-shaped shift for every
integer mantissa under the existing format assumptions. The real-value
rounding proof obtains nonnegativity from its original `inbetween_float`
hypothesis; no new public theorem premise or proof hole was added. Two
facade proof steps required explicit unfolding/rewrite/exact instead of
unbounded simplification to avoid deterministic heartbeat timeouts.

Verification receipts on the corrected snapshot:

- Full Lean 4.34.0 macOS library/test/executable build: **6,216 jobs**, exit 0,
  `/private/tmp/floatspec-raw-round-fix-build-v2-20260920.log`.
- Complete LSP error diagnostics clean for both edited implementation files,
  the nine-case fixture, and the updated six-part guided demo.
- Nine literal expected values checked independently in Lean and pinned Rocq;
  Lean also executes them and checks their equality in the kernel. Typed
  source-premise consumers pass in both languages. The six-part demo runs.
- All **197 saved counterexamples** replay successfully in both Lean paths
  and pinned Rocq, with 197 generated kernel assertions. They are committed
  in `scripts/fixtures/RawIEEERoundingReplay.json`, and the aggregate runner
  replays them independently of its chosen random seed. Receipt:
  `/private/tmp/floatspec-raw-round-fixed-replay-20260920/report.json`,
  14.613 seconds, source SHA-256
  `266add04c6a2f15ff1209bf1b77c6f55e2d64c975f3aaef67b8a24ec9efebbd7`.
- **38 live harness tests** pass in 114.787 seconds, including rounding-mode
  mutation rejection and preserved replay input validation. Log:
  `/private/tmp/floatspec-raw-round-fixed-harness-20260920.log`.
- The compiled trust audit checks **13,589 declarations / 58 modules** and
  exactly the same four named debts. The generated status is unchanged;
  157 source anchors validate.
- The complete repaired grid passes **6,354 shared cases and 6,354 kernel
  assertions**, seed 826411, 150 supplemental samples per format, in 513.270
  seconds. Receipt:
  `/private/tmp/floatspec-raw-round-fixed-grid-20260920/report.json`.
  Its source SHA-256 matches the successful counterexample replay above.

Failed setup/check attempts remain failures: the initial generator emitted
an unparenthesized inexact-location argument; its report has status `error`
with no completed comparisons. The overlapping first harness invocation was
interrupted (exit 130), then rerun after the generator correction. The first
post-fix project build failed on the two proof heartbeat timeouts noted
above; neither timeout was hidden by increasing the budget or adding sorries.
One Rocq fixture invocation used a different output basename, which Rocq
rejects; the corrected same-basename invocation passed.

Next independently reproduced finding, not yet corrected here: direct raw
overflow at precision 0 or -1 produces finite mantissa 0 in Lean, whereas
pinned Rocq's `Z.to_pos` fallback produces 1. Read-only paired probes are
`/private/tmp/RawOverflowProbe.lean` and `.v`. This is outside the overflow
validity theorem's positive-precision hypotheses, but still a total-function
discrepancy. It is kept separate from the signed-shift correction.

### September 20 continuation: preserve raw overflow's positive carrier

The separately recorded raw-overflow discrepancy is now corrected in both
`standard_binary_overflow` and `bsn_binary_overflow`. Pinned
`BinarySingleNaN.v:1182` uses `Z.to_pos (Zpower 2 prec - 1)`, which falls back
to positive 1 when its input is nonpositive. Lean had computed a natural
mantissa of 0 at precision 0 or below. A shared, explicitly Lean-local
`rawOverflowMantissa` now returns the ordinary `2^prec - 1` for positive
precision and 1 otherwise. Its positivity is proved for every integer
precision; a simp lemma preserves all existing positive-precision proofs.
No old theorem statement was weakened and no new sorry was introduced.

**Harness finding:** the previous overflow adapter enforced `0 < prec < emax`
on every input, although those are the validity theorem's hypotheses, not
the raw definition's domain. The broadened family accepts arbitrary integer
format parameters and retains 21 columns: SingleNaN output and validity,
the standard helper, two legacy full-float routes, and the exact positive-
mantissa full-float result. It deliberately observes all stages.

Before correction, seed 827419 with 100 supplemental samples found **87
disagreements in 680 cases**, all at nonpositive precision. The exact
`Binary.binary_overflow_exact` route already agreed because `SF2FF_exact`
itself restores a positive mantissa. Inspecting only that final conversion
would therefore have concealed the earlier mismatch. The failed report is
`/private/tmp/floatspec-raw-overflow-before-20260920/report.json`, 33.822
seconds, source SHA-256
`266add04c6a2f15ff1209bf1b77c6f55e2d64c975f3aaef67b8a24ec9efebbd7`.
Only 300 assertions from agreeing batches were generated in that failed run.

Verification on the corrected snapshot:

- Full macOS Lean 4.34.0 library/test/executable build: **6,216 jobs**, exit 0;
  `/private/tmp/floatspec-overflow-full-build-20260920.log`.
- Complete LSP error diagnostics clean for Binary, BinarySingleNaN, the
  source facade, and the new pure Lean fixture. Existing proofs stayed closed.
- Seven literal expected results in `RawOverflow.lean` and `.v` pass
  independently; the Lean side executes them and proves them by kernel
  reduction. The original four-row paired probe now prints identical results.
- All **87 original counterexamples** pass both Lean paths, pinned Rocq,
  and generated kernel assertions. They are retained in
  `scripts/fixtures/RawOverflowReplay.json`; receipt:
  `/private/tmp/floatspec-overflow-fixed-replay-20260920/report.json`,
  7.608 seconds. All **197 signed-rounding counterexamples** also replay
  successfully after this change, with 197 kernel assertions; receipt:
  `/private/tmp/floatspec-overflow-rounding-replay-20260920/report.json`,
  16.106 seconds. Both have source SHA-256
  `044d41ec21afcdbc8f8e396b932f22f1d7a539644046a76d62cc3f83fb6093f7`.
- **42 live harness tests** pass in 136.188 seconds. Five separate mutations
  replace each exported mantissa column with zero in turn; each is rejected
  in compiled Lean and kernel reduction. Log:
  `/private/tmp/floatspec-overflow-fixed-harness-20260920.log`.
- **160 source anchors** validate. The compiled trust audit checks
  **13,594 declarations / 58 modules / four existing named debts**.
- The fresh-seed combined grid passes **7,079 cases and 7,079 kernel
  assertions**: 730 overflow cases and 6,349 raw-rounding cases, seed 827421
  with 150 supplemental samples, in 564.272 seconds. Receipt:
  `/private/tmp/floatspec-overflow-round-fixed-grid-20260920/report.json`.
  Its source SHA-256 matches the two successful replays above.

The next independently reproduced execution gap is the proof-carrying
SingleNaN arithmetic API. `/private/tmp/SingleNaNExecutionGap.lean` fails
compiled calls to `Bplus`, `Bmult`, `Bdiv`, and `Bsqrt` solely on their
`noncomputable` declarations. Inspection of all six operation bodies against
pinned `BinarySingleNaN.v:1578,1940,2042,2094,2307,2466` shows source-shaped
integer branches and proof-only uses of reals. Enabling and cross-testing
these exports is next; the already-executable full-payload arithmetic tests
do not substitute for testing this separate SingleNaN API.
The six main correctness signatures were also compared with the compiled
Rocq types, including finite-input hypotheses for addition/subtraction/FMA,
the nonzero-real denominator premise for division, and signed-zero clauses.
No additional signature mismatch was found in this inspection; the real-sign
helper definitions were checked as part of that comparison.

### September 20 continuation: execute the separate SingleNaN arithmetic APIs

The six direct `BinarySingleNaN` arithmetic operations and their six
source-mode facade exports now compile. Their types and integer calculations
are unchanged. The finite-division helper is also executable. Square root's
real-valued `input` temporary had to move into its erased validity proof:
merely deleting `noncomputable` failed with `lean.dependsOnNoncomputable` on
`F2R`. The relocated proof remains closed, as do all existing correctness
theorems. Twelve pinned source anchors identify the six operations in both
namespaces; the extracted finite-division helper is explicitly Lean-local.

The `small_ieee` bridge now serializes **87 columns**, not 39. In addition to
input validity, the three converted inputs, and six full-payload results, it
calls all six direct SingleNaN operations and all six source-mode facade
operations. All three sets are compared with the actual pinned Rocq
SingleNaN operations. These Lean paths share helpers; this checks exported
wiring and executable behavior, not independence of three implementations.

The new paired `SingleNaNArithmetic.lean`/`.v` fixtures separately check
**30 literal one-bit-format answers** across the five modes and six operations.
The Lean fixture checks both SingleNaN APIs, by kernel reduction and compiled
execution. This includes nearest-even versus nearest-away at the underflow
midpoint, directed overflow, signed cancellation, square root, and
`fma(2,2,-2) = 2` despite overflow of the separately rounded product.
One-bit precision is deliberately outside the full-payload bridge's
`1 < prec < emax` domain: that bridge needs a valid nonzero NaN payload.
The combined runner includes the new pair. CI's Lean fixture list now also
includes Boolean comparisons and both raw-rounding regression fixtures;
this does not repair the separately known hosted cache/toolchain issue.

Verification completed before the broad integration run:

- The original four-call failing client now prints `true, true, false, true`
  for finiteness of zero addition, multiplication, division, and square root.
- Complete LSP error diagnostics are clean for the implementation, source
  facade, and new fixture. The library builds in 3,101 jobs; the explicit
  library/test/executable targets build in **6,215 jobs**, both exit 0.
  Logs: `/private/tmp/floatspec-single-nan-full-build-20260920.log` and
  `/private/tmp/floatspec-single-nan-tests-build-20260920.log`.
- All **42 live harness tests** pass in **142.137 seconds**. The arithmetic
  mutation test independently replaces addition with subtraction in each of
  the three public APIs. Every change is caught in both Lean execution paths;
  all untouched columns must continue matching. Log:
  `/private/tmp/floatspec-single-nan-harness-20260920.log`.
- The new one-bit fixture and the Boolean/raw-rounding/raw-overflow paired
  fixtures run successfully in both languages on this snapshot.
- **172 source anchors** validate. The compiled trust audit checks
  **13,590 declarations / 58 modules / four unchanged named debts**.
  Generated status files are unchanged.

The initial marker-only build remains a recorded failure in
`/private/tmp/floatspec-single-nan-executable-build-20260920.log`; its corrected
success is in the separate `...-build-v2-...` log. An initial two-test harness
attempt overlapped rebuilding the test artifacts and failed on a missing
`BitsExecution.olean`; it is not counted as a pass. All build processes
finished before the complete passing harness run and the frozen grid began.

A **27,771-case**, fresh-seed all-24-family run now passes, seed `828431`
with 40 supplemental samples, in **3,081.590 seconds**. All 27,771 cases
agree in compiled Lean, kernel reduction, and pinned Rocq, and all 27,771
generated kernel assertions pass. The retained
receipt is `/private/tmp/floatspec-single-nan-all-families-20260920/report.json`.
No port/library source edit or build overlapped this completed frozen run.

#### Independent tests added without changing the frozen library snapshot

The independent multiplication-error probe now passes in both languages:
**55 exact inputs and 5,385 conditional cases** in the three-bit format,
checking all five rounding modes. Inputs are independently enumerated; error
membership is checked against that enumeration in exact integer units, not
by asking the rounder to re-round its own output. The smallest positive
subnormal squared supplies a checked counterexample when the underflow
premise is omitted. The persistent fixtures are
`scripts/fixtures/MultiplicationErrorGrid.lean` and `.v`; explicit cardinality
assertions prevent an empty grid from passing vacuously. Lean checks the grid
by kernel reduction and compiled execution; Rocq checks it by `vm_compute`.
Both are wired into the conformance runner, and the Lean fixture into CI.

`scripts/fixtures/NativeSingleNaNArithmetic.lean` separately runs **200,200
native comparisons**: five operations through both direct and source-mode
SingleNaN APIs, for 10 boundary pairs plus 10,000 seeded pairs in each of
binary32 and binary64. Seed `831557` and exact input words are retained in
failure messages. Signed zeros are compared bit-for-bit; all NaNs are
explicitly quotiented. This tests nearest-even only, not directed rounding,
FMA, NaN payload propagation, or universal compiler/hardware correctness.
The persistent run passes in
`/private/tmp/floatspec-native-single-nan-persistent-20260920.log`.
Complete LSP error diagnostics are clean for both new Lean fixtures.

Deliberate mutations also fail as intended. Replacing multiplication with
addition makes the independent property grid fail both kernel reduction and
compiled execution (`/private/tmp/MultiplicationErrorGridMutation.out`).
Replacing only source-mode addition with subtraction breaks the native test
on `-0 + +0`, returning negative rather than positive zero
(`/private/tmp/NativeSingleNaNArithmeticMutation.out`). The replay row is
`[32,0,2147483648,0,0]`; the exact SingleNaN path is replayable through the
fixture's `observations32`, while `ieee_modes_bridge.py` can cross-check the
full-payload baseline on the same words.

These were standalone test fixtures and documentation edits. The completed
all-family run's port/library source SHA-256 remains
`17689e21deca9fc135815da4c8f10276cb6099dcc9c5b1568bc6b98d51e8ef66`;
there was no overlapping rebuild or port-source edit.

#### Contract repairs prepared outside the frozen snapshot

Comparing all eight compiled `Mult_error` signatures found that
`mult_error_FLT_ge_bpow` still requires `Prec_gt_0` in Lean, absent in Rocq.
The Pff nearest-even specialization has the same extra premise. The first
proof recompiles unchanged without it in a scratch module. The second proof
also closes after replacing an unnecessarily restricted zero-rounding helper.
The other seven multiplication signatures and four Sterbenz signatures match
the inspected source premises/conclusions, accounting for the redundant Lean
radix witness and representation conventions. This is a signature inspection,
not a review of every underlying definition or every proof step.

The restriction also occurs in the source-facing `round_to_generic` wrapper:
it requires `Valid_exp fexp`, whereas compiled Rocq `Generic_fmt.round` takes
an arbitrary exponent function and integer-rounding function. `round_0`
requires only validity of the integer-rounding function in Rocq. A paired
scratch example proves `fexp(e) = e + 1` is **not** a valid exponent function,
yet source rounding of zero is zero; an unrestricted copy of the identical
Lean rounding body and zero proof succeeds. Files:
`/private/tmp/RoundZeroNoValidity.lean` and `.v`.

Compiled source inspection additionally confirms no `Valid_exp` premise on
`round_generic`, `round_ext`, `round_opp`, `round_DN_opp`, `round_UP_opp`,
`round_ZR_opp`, `round_AW_opp`, `round_ZR_DN`, `round_ZR_UP`, `round_AW_UP`,
or `round_AW_DN`; their current Lean wrappers require it. This is not grounds
for blanket premise deletion: the inspected source `round_ZR_abs`,
`round_AW_abs`, and `round_abs_abs` **do** retain `Valid_exp`.
The source snapshots are retained in `/private/tmp/GenericRoundContracts.*`.
These contract repairs remain pending integration after the completed frozen run.
An isolated copy of the complete 8,280-line `Generic_fmt` module now compiles
after removing **17** unnecessary `Valid_exp` binders from the raw wrapper,
its structural laws, and corresponding compatibility helpers. Proof bodies
are unchanged. This is a successful preparation check, not yet a repository
integration build; the copy and diagnostics are
`/private/tmp/GenericFmtNoPremises.lean` and `.out`. The source-required
absolute-value and monotonicity premises are left intact.

#### Large-format SingleNaN cross-tests and remaining execution gaps

The independent native tests exposed a coverage gap, not an arithmetic
counterexample: the prior binary32/binary64 mode bridge called only the
full-payload API. It now has **57 columns**: the original nine exact input/
full-payload result words plus 24 constructor fields for direct SingleNaN
results and 24 for the source-mode facade. Each set calls the actual pinned
Rocq SingleNaN operation; NaNs are one constructor only in these latter APIs.
The full-payload NaN signs/payloads remain exact and separately observed.

All **nine live harness tests** pass in **34.481 seconds**, including new
independent add-to-subtract mutations of each SingleNaN API. Both compiled
and kernel Lean must reject the changed fields while all other columns still
match. Literal ties and NaN results check the serializer's layout. Log:
`/private/tmp/floatspec-single-nan-modes-harness-v2-20260920.log`.
A fresh **490-case** all-ten-format/mode-group run passes, seed `832561`,
with 20 supplemental samples per group, in **529.655 seconds**. All 490
compiled/kernel/Rocq rows agree, and all 490 generated kernel assertions pass:
`/private/tmp/floatspec-three-api-ieee-modes-20260920/report.json`.
Both completed bridges use the unchanged library snapshot recorded above.

A separate compiled client now reproduces seven remaining helper execution
gaps: `BinarySingleNaN.binary_normalize`, `Bone`, `Bldexp`, `Bfrexp`, `Bulp'`,
`Bpred_pos'`, and `Bsucc'`. Receipt:
`/private/tmp/SingleNaNRemainingExecutionGaps.out`. An isolated facade copy
with eight marker removals enables normalization, ldexp and frexp, but its
other branches still fail because the underlying `Binary.BoneSingle` and
`Binary.shr_fexp` aliases remain noncomputable. That partial preparation is
recorded as a failure, not a fix:
`/private/tmp/SingleNaNFacadeExecutable.out`. No repository implementation
change from this experiment was included in either frozen bridge snapshot.
The second isolated attempt supplies an identical executable copy of
`BoneSingle` and unfolds the shift alias to its already executable body.
It now compiles the complete facade and executes all seven probe calls:
`true, true, true, -11, true, true, true`. Log:
`/private/tmp/SingleNaNFacadeExecutable-v2.out`. This establishes a viable
marker-only repair path, not a repository integration result or a differential
test of every input. The source bodies for frexp, alternate ulp, positive
predecessor, and successor were compared with pinned lines 3042, 3173, 3453,
and 3661; their conditional correctness premises remain in scope for the
subsequent signature review.

The prepared source-premise slice now has a reproduced before/after gate:
all **20** guards in `/private/tmp/UpcomingPremiseGuards.lean` fail on the
current extra premises (exit 1, `/private/tmp/UpcomingPremiseGuards-before.out`).
The equivalent unrestricted Rocq clients in
`/private/tmp/GenericRoundingPremiseClients.v` compile against the pinned
reference. These failures are expected regression witnesses, not passing
repository tests; the implementation repair has not yet been applied.

After both bridges finished, a fresh explicit
`lake build FloatSpec FloatSpecTests FloatSpec.Test floatspec` also passed
**6,216 jobs**, exit 0, with no intervening library edits. Log:
`/private/tmp/floatspec-three-api-milestone-build-20260920.log`.

### September 20 continuation: integrate the structural rounding premise repairs

The prepared **20** source-premise corrections are now integrated: 17 raw
rounding/structural/helper signatures in `Core/Generic_fmt`, the zero adapter
in `Calc/Round`, and the general plus nearest-even multiplication-error lower
bounds in `Prop/Mult_error` and `Pff/Pff2Flocq`. All 17 generic proof bodies
are unchanged. The Calc zero contract is now an ordinary equality, with its
three callers migrated at the same time. No new proof hole is introduced.
The source-required validity premises on absolute-value and monotonicity
theorems remain intact; this is not blanket instance removal.

Verification on source SHA-256
`c84963297d71a2eb896c7cec2a59d3a7d2757f2a3817a7882fe089143e287ba2`:

- All 20 previously failing guards now pass unchanged, and the persistent
  test module has **72** production guards plus its five control invocations.
  The paired Rocq clients compile, including the invalid-exponent zero
  example and both unrestricted multiplication-error clients.
- The explicit macOS Lean 4.34 library/test/executable build passes **6,216
  jobs**, exit 0: `/private/tmp/floatspec-rounding-premises-build-v2-20260920.log`.
  The first build failed only on a new test client's positional argument to
  `Calc.Round.round_0`; giving `beta` and `fexp` by name fixed the client.
  The failed first log remains `/private/tmp/floatspec-rounding-premises-build-20260920.log`.
- Complete LSP error diagnostics are clean for all five changed production
  modules and the test module. The test editor initially reported unavailable
  diagnostics after import changes; it became clean only after the successful
  build and LSP restart. A separate 3,101-job default build also passed.
- **190 source anchors** validate. The compiled trust audit still covers
  **13,590 declarations / 58 modules / four existing named debts**. Generated
  status files are unchanged.
- A ten-case representative replay exercises both IEEE widths and every
  rounding mode through all three arithmetic APIs after the type-only changes.
  All compiled/kernel/Rocq rows and ten generated kernel equalities pass in
  **8.334 seconds**. Receipt:
  `/private/tmp/floatspec-rounding-premises-replay-20260920/report.json`.
  This is deliberately not a claim that the prior 27,771-case run was rerun
  on the changed types; the earlier frozen receipt keeps its original hash.
- The paired multiplication-error grid (5,385 cases), finite rounding oracle
  (35,845 cases, including 95 closed Lean kernel boundaries), integer oracle
  (5,125 cases), and one-bit arithmetic fixture (30 literal results) were
  re-executed in Lean and pinned Rocq after the repair; the combined command
  exits 0. The standalone oracle claim boundaries remain unchanged.

The focused review ledger lists the exact repaired/retained premise boundary.
The independently prepared executable-helper slice remains separate future
work; it is not part of this contract repair.

### September 20 continuation: execute the source helper APIs

Eleven unnecessary `noncomputable` markers are removed from the two signed
shift aliases, both constant-one constructors, and the source facade's
normalization, one, scaling, decomposition, alternate ulp, positive
predecessor, and successor. The algorithms and types are unchanged. The
shift aliases are explicitly local references to Rocq Stdlib `SpecFloat`
notation rather than falsely linked to an unrelated Flocq declaration.
Nine new source anchors bring the validated total to **199**.

The 6,216-job full build, complete LSP diagnostics for both production
modules and the new fixture, and compiled trust audit all pass. The latter
still records **13,590 declarations / 58 modules / four existing debts**.
Build and trust receipts are
`/private/tmp/floatspec-single-helper-full-build-20260920.log` and
`/private/tmp/floatspec-single-helper-trust-20260920.json`.
The original seven-call execution-failure probe now runs successfully.

`SingleNaNHelpers.lean` and `.v` independently check 13 literal helper
results, four decompositions, and two signed shifts. The one-bit `emax = 2`
case returns `(1, 0)` for decomposition of one; half is not representable
and source normalization is conditional on `2 < emax`. The larger bridge
adds a 25th family with 46 result fields, eight formats, all five modes,
both signs, signed raw normalization, exceptional values, and observed
invalid raw-carrier validity before conversion. The first **45** live
harness tests pass, including five independently rejected helper mutations.
Log: `/private/tmp/floatspec-single-helper-harness-20260920.log`.

The same fixture subsequently gained two closed domain counterexamples:
`Bulp'(+infinity) = 1/16` differs from `Bulp(+infinity) = +infinity`, and
`Bpred_pos'(-1) = -1` differs from `Bpred(-1) = -1.25`. The latter algorithm
is intentionally positive-only. Both assistants check the inequalities;
Lean also executes them and has complete clean LSP diagnostics. Log:
`/private/tmp/floatspec-single-helper-fixture-v2-20260920.log`.
Twelve compiled helper signatures were compared with pinned Rocq and found
to retain the inspected source premises/conclusions. The focused source
review records the precise domain, including `Bfrexp`'s weaker requirement
of positive precision without `prec < emax`.

The first seed-`835627` 1,900-case run failed at a test-tool resource limit
after **1,650 compared/compiled/kernel-regression cases** with no numerical
mismatch. Lean's default exponentiation threshold refused a binary64 power;
the strict parser correctly rejected diagnostic-bearing output. Receipt:
`/private/tmp/floatspec-single-helper-grid-20260920/report.json`, status
**error**, exit 1. No prior receipt is overwritten or reclassified.
The bridge header now uses the bounded test-only threshold 5,000 already
used by the other IEEE bridges; the production implementation is unchanged.
A new live test reproduces the failure without that option, then checks
complete three-path agreement and a kernel regression with it. Its first
attempt over-specified the exact exponent in the expected warning; the
corrected test accepts any numeric exponent and passes in 8.648 seconds:
`/private/tmp/floatspec-single-helper-threshold-test-v2-20260920.log`.
The full rerun passes **1,900 compared cases / 1,900 compiled cases /
1,900 generated kernel equalities** in **335.909 seconds**, exit 0, on
unchanged library SHA-256
`6110bb056804058cb0606007b0a2721296f7355a464e98269772aee1d046ccb3`.
Receipt: `/private/tmp/floatspec-single-helper-grid-v2-20260920/report.json`.
The complete updated harness then passes **46 tests in 168.331 seconds**,
including the resource-limit regression and all earlier live mutations:
`/private/tmp/floatspec-single-helper-harness-v2-20260920.log`.
After the frozen run and harness completed, the explicit full build passed
again, **6,216 jobs**, exit 0:
`/private/tmp/floatspec-single-helper-final-build-20260920.log`.

A separate compiled recheck corrects one claim in the earlier double-rounding
review: Rocq discards unused section positivity variables. The FLX/FLT
multiplication statements already have no positivity binders, and FTZ retains
only the first precision's positivity, exactly as in the Lean public exports.
The three public square-root exponent-hypothesis helpers and both same-place
midpoint lemmas also match the inspected compiled source premises. No port
definition or theorem changed for this documentation correction. The first
scratch Rocq import used `From Flocq Require Import Prop...`, which fails
because `Prop` is a keyword; its corrected qualified import succeeds. Both
attempts remain in `/private/tmp/DoubleRoundCompiledContracts*.out`.

### September 20 continuation: test the complete frexp parameter domain

The combined helper family necessarily shared `0 < prec < emax`, but
compiled Rocq and Lean `Bfrexp` require only positive precision. A separate
26th bridge family now accepts that actual source type, including precision
equal to or greater than `emax` and nonpositive maximum exponents. Eleven
fields retain input validity, converted input, fraction, exponent and output
validity. Five literal rows and independent mutations of the fraction and
exponent pass in compiled Lean, kernel reduction and pinned Rocq. The three
new targeted harness tests pass in **11.122 seconds**. The complete harness
then passes **49 tests in 188.932 seconds**, before adding the independent-law
mutation described below. No production definition or theorem was changed.

The paired `SingleNaNHelpers` fixture now includes eight decompositions,
with four additional calls that have no `Prec_lt_emax` instance. In particular,
eight-bit precision with `emax = 2` returns `(1/128, 0)` for `1/128`, while
`emax = 3` returns `(-1/2, -7)` for `-1/256`. Signed zero in a source-legal
negative-maximum-exponent parameterization retains the specified sentinel.
Both assistants close these literal results; Lean executes them and has
complete clean LSP diagnostics.

New paired `FrexpLaws.lean` / `.v` fixtures independently check **6,772** raw
finite encodings. An explicit integer format-membership test admits **2,086**
finite values and rejects **4,686** encodings. For the valid values, the
checks require sign preservation, validity of the fraction, exact dyadic
reconstruction, and the `[1/2, 1)` fraction bound only when `2 < emax`.
Rejected encodings must convert to NaN with the source sentinel exponent.
The test oracle uses integer powers/comparisons, not the port's real-valued
correctness theorem or its validity predicate. Both full grid proofs close
by reduction; compiled Lean also passes. Rocq emits its standard large-Nat
notation warning, not a failed proof. Logs:
`/private/tmp/floatspec-frexp-independent-lean-v2-20260920.log` and
`/private/tmp/floatspec-frexp-independent-rocq-20260920.log`.

Adding one to the returned exponent fails both the closed kernel assertion
and the compiled check, exit 1 (`/private/tmp/FrexpLawsMutation.out`). That
mutation is now a persistent live harness test, and both pure fixtures
are wired into the standard runner/CI fixture loop. The complete harness
rerun passes **50 tests in 193.220 seconds**:
`/private/tmp/floatspec-frexp-domain-harness-v2-20260920.log`.
The seed-`836647` run also passes **4,169 compared/compiled cases and 4,169
generated kernel equalities** in **541.930 seconds**, exit 0, on unchanged
library SHA-256 `6110bb056804058cb0606007b0a2721296f7355a464e98269772aee1d046ccb3`.
Receipt: `/private/tmp/floatspec-frexp-domain-grid-20260920/report.json`.
Its **40** parameter pairs include **3,455** inputs with `prec >= emax`,
**2,406** with `emax <= 2`, and **1,763** with `emax > 2`. These counts
describe the finite corpus, not proof coverage of all integer parameters.
After both frozen verifications completed, the full macOS Lean 4.34 build
passed **6,216 jobs**, exit 0:
`/private/tmp/floatspec-frexp-domain-final-build-20260920.log`.

### September 20 continuation: direct division source contracts

`Calc.Div.mag_div_F2R` now states pinned `Calc/Div.v:48`'s integer digit-count
bounds directly. Its former Hoare wrapper ignored the dummy computation's
result and gave abstract magnitude bounds; these are related mathematically,
but required extra rewrites in both downstream clients. The unused projection
is removed. `Fdiv_core_correct` now exposes line 70's ordinary quotient-location
proposition, with its caller migrated. Both derive radix validity from the
existing carrier, rather than demanding an additional explicit argument.
All changed proofs remain closed and all numerical algorithm bodies are
unchanged. This is an interface mismatch repair, not a numerical bug finding.

The two standalone typed clients fail before and pass after the repair:
`/private/tmp/DivisionContractGuards-before.out` and `-after.out`.
They are now persistent in `SourcePremiseContracts.lean`, paired with exact
Rocq consumer types. The first Rocq fixture attempt omitted the Bracket import
and failed; the corrected fixture passes, exit 0:
`/private/tmp/floatspec-division-contract-rocq-v2-20260920.log`.
Initial Lean fixture diagnostics exposed ambiguous compatibility aliases for
`F2R` and `mag`; explicit qualification resolves them. Final complete LSP error
diagnostics are clean for Div, BinarySingleNaN, and SourcePremiseContracts.
The preliminary proof prototypes and their failed simplification attempts
remain in `/private/tmp/DivisionSourceContract*.out`.

The library-only build passes **3,101 jobs**; the explicit library/test/
executable build passes **6,216 jobs**, exit 0:
`/private/tmp/floatspec-division-contract-full-build-20260920.log` and
`/private/tmp/floatspec-division-contract-all-targets-20260920.log`.
Fresh compiled source metadata validates **201** anchors. The trust audit
observes **13,588 declarations in 58 modules**, with exactly the four existing
manifest debts and no added project axioms, unsafe declarations, runtime
overrides, or unexpected axioms:
`/private/tmp/floatspec-division-contract-trust-20260920.json`.

On frozen source SHA-256
`583be3cf37934ac34920b5221c69a9b460ea8d636fe8d5ed1394a5b420c237f5`,
seed `837661` passes **1,994 compared/compiled cases and 1,994 generated kernel
equalities** in **80.179 seconds**: 694 core division and 1,300 format-calculation
cases. Both exponent branches and zero/negative raw operands are exercised;
the latter are total-function checks, not witnesses of the positive-input
correctness theorem. Receipt:
`/private/tmp/floatspec-division-contract-grid-20260920/report.json`.
The ten saved binary32/binary64 rows also pass all five modes through all
three public arithmetic APIs, with ten generated kernel equalities, in
**8.288 seconds**:
`/private/tmp/floatspec-division-contract-modes-20260920/report.json`.
Both use the explicitly prebuilt snapshot (`fresh_build: false`); no library
edits or overlapping builds occurred during execution. Earlier larger
receipts retain their original hashes rather than being relabeled.

### September 20 continuation: square-root premise and independent Calc brackets

Compiled pinned Rocq `Fsqrt_correct` requires no `Valid_exp` instance. The Lean
export now matches that domain; its existing closed proof is unchanged except
for the magnitude lemma call. `mag_sqrt_F2R` now derives radix validity from
the carrier. The core theorem retains positive-mantissa and exponent premises.
Three source anchors and paired typed consumers cover all three statements;
one new compiler guard brings the total to **73**. The two Lean clients fail
before and pass after the correction (`/private/tmp/SqrtContractGuards-before.out`
and `-after.out`). Compiled Rocq output is in `SqrtContractGuards-rocq-v3.out`;
the earlier scratch attempts retain the missing magnitude coercion and explicit
radix-argument errors. Persistent paired consumers compile successfully.

New `CalcBrackets.lean` / `.v` fixtures close **8,640 division** and **2,496
square-root** checks in bases 2, 3, and 10. Clearing positive denominators turns
the interval and midpoint conditions into integer inequalities. No second
divider/square-root implementation or correctness theorem provides the oracle.
The paired literals check seven-thirds at two output exponents and demonstrate
failure if square root's `2 * target <= inputExponent` premise is discarded.
The complete grids are kernel-checked in Lean and proved by computation in
Rocq; Lean also runs them. Isolated final logs:
`/private/tmp/floatspec-calc-brackets-isolated-lean-20260920.log` and
`/private/tmp/floatspec-calc-brackets-isolated-rocq-20260920.log`.
Initial fixture attempts had an ambiguous Lean `compare` and a nonexistent
Rocq comparison-equality helper; corrected qualified integer comparison and
an explicit comparison match resolve them. Rocq's large-Nat notation warning
is nonfatal. The first two mutation harness attempts over-specified Lean's
diagnostic wording; the corrected gate requires a failed closed literal
assertion and the compiled runtime failure. Both mantissa and location
mutations are checked independently for both operations. These fixtures are
now included in the standard runner and Lean CI fixture list; no hosted-CI
success is claimed.

**Concurrent checkout change, preserved rather than hidden:** a separate Claude
daemon created `ComputableCompare.lean` and switched the original checkout to
its own branch during verification. The seed-`838673` shared-checkout bridge
correctly fails after **200 agreeing cases**, status **error**, because the
source fingerprint changed:
`/private/tmp/floatspec-sqrt-contract-grid-20260920/report.json`.
The original 52-test harness run also fails with three errors in 240.448 seconds:
one concurrent-source guard and two attempted builds of the daemon's incomplete
new module. It remains a failed run:
`/private/tmp/floatspec-calc-bracket-harness-v3-20260920.log`.

The continuation now uses the managed worktree
`/Users/alokbeniwal/.codex/worktrees/astra-flocq-continuation/FloatSpec`, on
`codex/astra-flocq-audit`. Only this slice's own changes were transferred there;
after exact-content checks, they were removed from the original checkout,
leaving the daemon's files and pre-existing `Deps/flocq` state intact.
Dependency/build files were copied using APFS copy-on-write cloning, not shared
writable artifact paths. The isolated full build passes **6,216 jobs**;
complete LSP diagnostics are clean for the changed source, contract clients,
and bracket fixture. The isolated trust audit observes **13,588 declarations
in 58 modules**, exactly four debts, and no new trust hazards:
`/private/tmp/floatspec-sqrt-isolated-trust-20260920.json`.
Fresh compiled metadata validates **204** source anchors.

All **52** live core-harness tests pass in the isolated tree in **200.362 seconds**:
`/private/tmp/floatspec-calc-bracket-isolated-harness-20260920.log`.
An initial isolated grid also passed, but overlapped harness build checks;
the authoritative final sequence is the full build followed by the serial
bridge, with no overlapping builds or source edits. Build log:
`/private/tmp/floatspec-sqrt-isolated-final-build-20260920.log`.
On SHA-256 `0a4e035d923b1287b23b1483bb89e7883e9eddd9e3a55e1f86459864ef39b169`,
seed `838673` passes **1,565 compared/compiled cases and 1,565 generated kernel
equalities** in **64.296 seconds**: 265 core square-root and 1,300
format-calculation cases. Receipt:
`/private/tmp/floatspec-sqrt-isolated-serial-grid-20260920/report.json`.
The guide now explains these brackets and premise distinctions linearly.
Neither this finite evidence nor the source anchors certify all of Calc.

### September 20 continuation: distinguish FTZ inclusion directions

Compiled source inspection confirms that `FLXN_format_FTZ` (FTZ.v:71) and
`generic_format_FTZ` (line 80) take no positive-precision premise. Both Lean
exports inherited `Fact (0 < prec)`. The normalized projection now drops that
section instance; the existing private generic-inclusion proof omits it too.
The generic public theorem calls the unrestricted forward helper directly,
rather than projecting it from the equivalence that also contains the
restricted reverse direction. Mathematical proof bodies and executable
definitions are unchanged. Reverse inclusion, FTZ-from-normalized membership,
and the `satisfies_any` source contracts retain their precision premises.

Paired compiled types are retained in `/private/tmp/FTZCompiledContracts-lean.out`
and `-rocq.out`. Two exact Lean clients fail before and pass after the repair:
`/private/tmp/FTZPremiseGuards-before.out` and `-after.out`; the matching Rocq
clients compile. Persistent tests now include both clients and universal zero
membership at arbitrary integer precision. The premise checker additionally
tests the `Fact` encoding, including a deliberately leaking declaration.
There are **75** production premise guards, five deliberate negative controls,
and one selective-parameter positive control. The first target build failed
because `omit` followed a docstring; moving the theorem into a section without
the instance resolves that syntax issue. Initial paired fixture attempts
also lacked the explicit FTZ imports. These failures are retained in the
`floatspec-ftz-inclusion-target-20260920.log` and `-rocq-20260920.log` receipts.

After correction, complete LSP error diagnostics are clean for FTZ,
FTZSourceShape, and SourcePremiseContracts. The latter two files also execute
as standalone Lean clients, exit 0. The Rocq client passes, exit 0:
`/private/tmp/floatspec-ftz-inclusion-rocq-v2-20260920.log`.
The explicit full macOS Lean 4.34 build passes **6,216 jobs**, exit 0:
`/private/tmp/floatspec-ftz-inclusion-final-build-20260920.log`.
Fresh metadata validates **206** anchors; the compiled trust audit still
observes **13,588 declarations / 58 modules / four unchanged debts**, with
no additional trust hazards. Its report is
`/private/tmp/floatspec-ftz-inclusion-trust-20260920.json`.

Frozen source SHA-256
`a0f5d5b372d23304bb11b227e62ac1a18dd4c994fd51f9aa6a25f32dcd8c550d`
passes **1,724 compared/compiled cases and 1,724 generated kernel equalities**
in **70.556 seconds**, seed `839681`: 374 exponent-function cases and 1,350
format-calculation cases, including nonpositive precision. Receipt:
`/private/tmp/floatspec-ftz-inclusion-grid-20260920/report.json`.
The build/metadata/trust steps completed before this serial bridge; no source
edits or builds overlapped it. Runtime agreement is a regression check for
this type-only change, not a proof of the real-valued inclusion theorem.
The FTZ docstrings and linear guide now distinguish the witness predicate,
its generic characterization, the actual small-magnitude exponent
`emin + prec - 1`, and the separate integer-rounding policy.

### September 20 continuation: remaining normalization execution blockers

Three minimal compiled clients failed on `Binary.binary_normalize`, the
root raw `binary_normalize`, and `binaryRoundAuxToBinarySingleNaNFloat`.
Only their `noncomputable` markers were removed; bodies and type signatures
are unchanged. The full-payload normalizer is linked to `Binary.v:1019`.
The raw compatibility carrier and explicit validity adapter are classified
as local, not falsely labeled as exact source interfaces.
Before/after receipts are
`/private/tmp/RemainingNormalizationGaps-isolated-before.out` and
`-after.out`. Compiled source/Lean signatures are retained in
`/private/tmp/NormalizationContracts-{lean,rocq}.out`: the two source-facing
normalizers require positive precision and precision less than the maximum
exponent; the local raw compatibility interfaces have different contracts.

The new `normalize` bridge family observes three public entry points
separately in twelve columns. The `ieee_round` family grows from sixteen to
twenty-one columns, retaining all earlier raw observations and separately
observing the validity adapter. Its explicit validity bit distinguishes a
rejected finite result from a valid NaN. Both streams use the actual source
algorithm, with no alternate rounding algorithm hidden in the adapter.

Paired pure fixtures pass **150 normalization observations** (three APIs,
five modes) and **six validity-adapter boundaries**. Expected results are
literal, covering both zero signs, even/odd halfway cases, underflow and
overflow. The first fixture incorrectly expected precision-zero rounding
to produce an invalid result; both provers rejected that oracle because
the actual result was a valid zero. That zero case is now retained beside
a genuinely invalid finite overflow at `prec = 3, emax = 0`. An initial
Lean runtime check also needed an explicitly typed expected-row definition.
The failed receipts remain
`/private/tmp/floatspec-normalization-pure-{lean,rocq}-20260920.log` and
`/private/tmp/floatspec-round-adapter-focused-20260920.log`.
The corrected paired fixtures and complete LSP diagnostics pass; final logs
are `/private/tmp/floatspec-normalization-pure-{lean,rocq}-final-20260920.log`.

All **57** live core-harness tests pass in **231.004 seconds**:
`/private/tmp/floatspec-normalization-full-harness-20260920.log`.
New mutations change one normalization export at a time, and separately
corrupt adapter validity and payload columns. Both Lean execution paths
must disagree with Rocq while unrelated columns remain unchanged.
Fresh compiled metadata checks **207** source anchors; the trust report
still observes **13,588 source declarations / 58 modules / four debts**.
The default-library build passes 3,101 jobs. On frozen source SHA-256
`a1157e49442726ed62f05d601f267b3efa85bc5f7e257a279cc258a89ece328d`,
the serial differential run passes **9,346 compared/compiled cases and
9,346 generated kernel equalities** in **1,193.671 seconds**, seed
`840691`: 6,342 raw-rounding cases and 3,004 normalization cases.
Receipt: `/private/tmp/floatspec-normalization-grid-20260920/report.json`.
After the bridge finishes, the explicit
`lake build FloatSpecLib FloatSpecTests floatspec` passes **6,216 jobs**:
`/private/tmp/floatspec-normalization-all-targets-20260920.log`.
No product source edits or builds overlapped the differential run. The
default-library build and trust/metadata checks preceded it; the all-target
cross-check followed it. These are finite execution and closed-client
checks, not a whole-port equivalence proof.

### Further findings prepared without changing the running snapshot

Six FLT exports retain positive-precision premises absent from compiled Rocq:
`cexp_FLT_FLX`, `generic_format_FLT_FLX`, `generic_format_FLX_FLT`,
`round_FLT_FLX`, `cexp_FLT_FIX`, and `generic_format_FIX_FLT`.
All six exact unrestricted Rocq clients pass; the corresponding Lean clients
fail on the extra premise or legacy packed Hoare argument. A scratch copy
removes those premises, makes five claims direct propositions, and closes
the existing proofs. The production source has not yet changed.
The nearby `generic_format_FLT_FIX` really does retain positive precision
in the source. Paired closed counterexamples show why: at precision zero,
one belongs to FIX with exponent zero but not FLT with minimum exponent zero,
even though it meets the claimed upper-bound condition.

Receipts:
`/private/tmp/FLTCompiledContracts20260920-{lean,rocq}.out`,
`/private/tmp/FLTUnrestrictedClients20260920-before.out`,
`/private/tmp/FLTUnrestrictedClients20260920-rocq.out`, and
`/private/tmp/FLTUnrestrictedDraft20260920-v2.out`.
The first standalone draft inherited default style linters, unlike the Lake
build; the second uses the project's existing style settings and passes.
Counterexamples:
`/private/tmp/FLTZeroPrecisionCounterexample.out` and
`/private/tmp/FLTZeroPrecisionCounterexample-rocq-v2.out`.

Reading the separate Claude comparison branch exposed a more substantive
raw-interface mismatch in the existing port. For positive finite encodings
`(3,-1)` and `(6,-2)`, both mathematical values are 1.5. At the normalization
checkpoint, `FaithfulPrimFloat.SFeqb` said true, proved by a closed Lean calculation.
Rocq 9.2's actual raw `SpecFloat.SFcompare` returns `Some Gt`, and
`SFeqb` returns false: it compares exponent then mantissa and relies on
canonicality for that order to mean numerical order. Its
[pinned Corelib definition](https://github.com/rocq-prover/rocq/blob/adfbf1855c348766beb4b790dcc8ebc02f908f63/theories/Corelib/Floats/SpecFloat.v#L177)
matches the inspected compiled definition. The raw comparison has no
canonicality argument, so total-function correspondence must retain that
behavior rather than silently reinterpret noncanonical inputs by real value.
This is not a counterexample to comparison of valid binary64 operands.

The mismatch originates in `c55f3805`, which predates upstream `158263e9`
and the Sol audit range. Claude's separate `ff02ad28`/`f5d01e1d` additions
preserve this real-valued interpretation in new `*C` APIs; they do not repair
the raw source mismatch. Their guide's claim that Rocq's raw comparison is
defined through reals is incorrect. That branch remains preserved and is not
integrated into this audit branch. A scratch source-shaped replacement
already typechecks with a closed structural equality to the generic
proof-carrying comparator. The production fix and cross-test were pending at
that checkpoint; the completed comparison milestone follows below.
Receipts: `/private/tmp/RawSpecFloatComparisonAudit-lean.out`,
`/private/tmp/RawSpecFloatComparisonAudit-v2.out`,
`/private/tmp/RawSourceComparisonDraft-v3.out`, and
`/private/tmp/PrimitiveSourceComparisonDraft20260920.out`.
The scratch primitive module has only the same three pre-existing native
proof warnings; no new holes were added.

### Raw primitive comparison correction — 2026-09-20 11:33 UTC

The four raw `FaithfulPrimFloat` comparison definitions now use Rocq's
constructor/sign/exponent/mantissa branches. Their external Corelib links pin
the peeled Rocq 9.2.0 release commit, and the `flocq_local` reason explicitly
distinguishes imported runtime-library definitions from Flocq-owned source.
The source finite mantissa is positive; the shared corpus rejects the extra
zero-mantissa values admitted by Lean's raw Nat carrier.

The eight primitive/proof-carrying wrappers have unchanged bodies and types,
but no longer need `noncomputable`. All twelve APIs execute at their original
names. The new closed `SFcompare_B2SF` theorem relates raw comparison to the
generic proof-carrying comparator for every format. The native-model proof is
now structural; obsolete private real-ordering helpers are removed while the
public binary32/64 statements stay unchanged. No new proof debt is introduced.

The new `prim_comparison` bridge keeps fourteen columns: four raw results,
two validity flags, four primitive results, and four proof-carrying results.
Rocq's middle group executes actual native primitives; its raw and final
groups execute integer definitions. Noncanonical inputs are observed before
conversion, so their rejection into NaN cannot mask a raw discrepancy.
Paired `PrimitiveComparison.lean/.v` fixtures check 24 literal cases through
twelve independently called APIs and close both the equal-real-value and
unequal-raw-comparison claims. Four persistent inputs in
`PrimitiveComparisonReplay.json` retain the discovered source-contract boundary.

Verified on library SHA-256
`e7aaab7a915883488c73755254e6367454ee31d427be9d9771fa745ac88417c1`:

- **6,116** cases agree in compiled Lean, kernel reduction, and pinned Rocq,
  with **6,116** generated kernel equalities: 687 binary32 order cases,
  687 binary64 order cases, 3,317 generic comparison cases, and 1,425 new
  primitive/raw cases. The latter include 416 valid input pairs and 1,009
  with at least one rejected operand. Seed `841709`, 200 supplemental samples,
  batch size 50; **810.493 seconds**. All inputs and outputs are retained in
  `/private/tmp/floatspec-primitive-comparison-grid-20260920/`.
- The four permanent raw-interface replay inputs separately pass all three
  paths and four generated kernel equalities:
  `/private/tmp/floatspec-primitive-comparison-replay-20260920/report.json`.
- The full core harness passes **60 tests in 257.369 seconds**, including
  twelve deliberate mutations, each detected in both Lean paths and changing
  exactly its own comparison column. Receipt:
  `/private/tmp/floatspec-primitive-comparison-full-harness-20260920.log`.
- The explicit library/test/executable build passes **6,216 jobs**:
  `/private/tmp/floatspec-primitive-comparison-all-targets-20260920.log`.
  Changed source files and the Lean fixture have complete, error-free LSP
  diagnostics. The pure fixture receipts are
  `/private/tmp/floatspec-primitive-comparison-pure-lean-20260920.log` and
  `/private/tmp/floatspec-primitive-comparison-pure-rocq-final-20260920.log`.
- The existing native order loop is re-executed, including 200,000 order
  comparisons and 600,000 Boolean comparisons. The separate eight-case
  Boolean fixture also passes; its printed axiom sets contain no sorry.
  Receipts end in `native-order-20260920.log` and `booleans-20260920.log`
  under the same `/private/tmp/floatspec-primitive-comparison-` prefix.
- Fresh source metadata validates **207 anchors**. The compiled trust gate
  sees **13,532 declarations in 58 modules**, exactly the same four direct
  and transitive named proof debts, and no unexpected project axioms,
  unsafe declarations, or runtime overrides. The lower declaration count
  reflects deleted private proof machinery, not newly admitted proofs.
  Receipts: `/private/tmp/floatspec-primitive-comparison-anchors-20260920.log`
  and `/private/tmp/floatspec-primitive-comparison-trust-20260920.json`.

No imported source edits or builds overlapped the authoritative bridge run.
The first smoke attempt failed because unqualified Rocq comparison constructors
were parsed ambiguously; fully qualified names fixed the serializer, and the
second attempt passed all three paths and generated equalities. Initial pure
Rocq attempts needed an explicit radix import and normalization of two integer
powers before the real-field proof; only the final successful attempt is
counted. Failed logs remain available beside the passing receipts.

This corrects a total source API, not an observed hardware comparison failure.
Finite agreement, structural Lean proofs, and whole-library source equivalence
remain distinct claims.

### Next prepared slices, not production changes

The FLT inspection now identifies **eleven** unnecessary positive-precision
premises: the six inclusion/exponent/rounding exports listed above, plus
`ulp_FLT_le`, `ulp_FLT_exact_shift`, `succ_FLT_exact_shift_pos`,
`succ_FLT_exact_shift`, and `pred_FLT_exact_shift`. The neighboring
`ulp_FLT_gt`, `ulp_FLT_pred_pos`, and reverse format inclusion retain that
premise in compiled Rocq. All eleven unrestricted Rocq clients compile,
while the current Lean client set fails. A scratch module with direct
propositions closes every proof without new holes. A private predecessor
helper used a nonnegative-input lemma whose zero case required validity;
its actual strictly positive branch can be discharged directly from the
definition, avoiding that unnecessary dependency.

Receipts: `/private/tmp/FLTRemainingContracts20260920-{lean,rocq}.out`,
`/private/tmp/FLT11UnrestrictedClients20260920-{before,rocq}.out`, and
`/private/tmp/FLTAllDirectDraft20260920.out`. Earlier scratch attempts that
exposed the helper dependency remain recorded as failures.

Separately, 33 remaining primitive definitions and four arithmetic instances
compile in a scratch copy after removing only `noncomputable` markers.
Thirty-seven independent clients fail in the current production module:
`/private/tmp/PrimitiveExecutionClients-before-20260920.out`.
The first scratch module still failed because the arithmetic instances
retained their markers; the second passes with only the same three native
proof warnings: `/private/tmp/PrimitiveExecutableDraftV2_20260920.out`.
These changes need production integration and actual boundary/cross-tests
before becoming a completed execution milestone.

### September 20, 11:55 UTC — eleven FLT contracts repaired

The eleven candidates above are now production corrections. Each compiled
Rocq export omits positive precision; each Lean export now does too.
Ten legacy Hoare wrappers become direct propositions, while the rounding
equality was already direct. Callers in `Plus_error`, `Mult_error`, and
`Div_sqrt_error` migrate together. Eleven pinned source anchors identify the
checked statements. All existing proofs close; no algorithm body or proof-debt
manifest changes.

The private positive-predecessor helper no longer imports a validity premise
through a lemma that also handles zero. Its strictly positive branch reduces
directly from the definitions. The signed successor/predecessor retain their
stronger `+1` magnitude bounds; the positive successor retains the source's
weaker bounds. A copied source comment was corrected accordingly.

Positive precision remains on the genuinely restricted reverse inclusion and
neighboring `FLT_format_generic`, `ulp_FLT_gt`, and `ulp_FLT_pred_pos`.
The paired permanent fixtures prove a counterexample at base two, precision
zero, minimum exponent zero, and value one: the reverse theorem's size bound
holds, FIX membership holds, but FLT membership does not. This is a closed
proof in each prover, not merely a failed search for a proof.

Verification on library SHA-256
`f5dc4646d4bc0ed7ce862bb00a3620507d525a304f3b9c73a3a7de904f8d89e7`:

- Eleven unrestricted typed clients compile in each prover; the Lean fixture
  now checks **86 production premise guards**, with the existing five deliberate
  negative controls. The paired reverse-inclusion counterexample also passes.
  Receipts: `/private/tmp/floatspec-flt-eleven-pure-lean-20260920.log` and
  `/private/tmp/floatspec-flt-eleven-clients-rocq-v3-20260920.log`.
- The full explicit library/test/executable build passes **6,216 jobs**:
  `/private/tmp/floatspec-flt-eleven-all-targets-20260920.log`.
  Complete error-free LSP diagnostics were obtained for all four changed
  source modules and `SourcePremiseContracts.lean`. The stale LSP initially
  returned `diagnostics_unavailable`, not a pass; a build/server restart
  restored complete diagnostics.
- Fresh metadata validates **218 source anchors**. The compiled trust gate
  reports **13,532 declarations in 58 modules** with the same **four** named
  direct/transitive proof debts and no unexpected project axioms, unsafe
  declarations, or runtime overrides. Receipts end in
  `anchors-20260920.log` and `trust-20260920.json` under the same prefix.
- **1,813 differential cases** agree in compiled Lean, kernel reduction,
  and pinned Rocq, with **1,813 generated kernel equalities**. Seed `842729`,
  200 supplemental samples, batch size 50; **209.176 seconds**.
  The 413 format cases include **127 with nonpositive precision**; the other
  1,400 exercise format-driven integer calculations. All replay inputs,
  outputs, and the report remain in
  `/private/tmp/floatspec-flt-eleven-grid-20260920/`.
  No imported-source edits or library builds overlapped this authoritative run.
- The source-anchor self-tests and compiled-trust mutation controls pass:
  `/private/tmp/floatspec-flt-eleven-anchor-tests-20260920.log` and
  `/private/tmp/floatspec-flt-eleven-trust-tests-20260920.log`.

The first integrated Lean client build failed because the broad test import
made unqualified `cexp` and `generic_format` ambiguous. Explicit qualification
fixed the test. The first integrated Rocq counterexample failed because the
fixture did not import `Lra`; the explicit import fixed it. Both failed logs
remain next to their successful reruns and are not counted as passes.
Earlier scratch failures exposing the helper's extra premise remain recorded.

The full core harness also passes **60 tests in 255.632 seconds** on this
snapshot, including the existing arithmetic, serializer, mutation, timeout,
interruption, and concurrent-source-change controls:
`/private/tmp/floatspec-flt-eleven-full-harness-20260920.log`.

This is a theorem-interface correction, not a discovered numerical mismatch.
The finite grid does not prove the eleven universal statements; their closed
Lean proofs do. Neither those proofs nor the grid certify whole-port source
equivalence. The separate Claude checkout still has its original submodule
modification and three independent comparison commits, preserved untouched.

### Next confirmed finding — total primitive conversion

Fresh execution finds a separate total-interface mismatch in
`FaithfulPrimFloat.SF2Prim`: the Lean definition rejects every invalid raw
encoding as NaN, whereas Rocq's `FloatOps.SF2Prim` numerically converts the
mantissa through an unsigned 63-bit word, rounds that integer, then scales
and rounds again. The current roundtrip theorems only cover valid inputs and
therefore do not detect this mismatch.

Four raw positive-mantissa cases return NaN in Lean but respectively `1.5`,
positive zero, `1`, and mantissa `1125899906842624` at exponent `-1074` in
Rocq. Their inputs are `(3,-1)`, `(2^63,0)`, `(2^63+1,0)`, and
`(2^53+5,-1077)`. The last case distinguishes the source's double rounding
from one-shot normalization, which instead returns mantissa
`1125899906842625` at exponent `-1074`. A repair must preserve both unsigned
wrapping and the two rounding stages; replacing rejection by one rounding
operation would still be wrong.

Receipts: `/private/tmp/SF2PrimTotalCounterexamples20260920-lean-before-v2.out`
and `/private/tmp/SF2PrimTotalCounterexamples20260920-rocq.out`, with both
source fixtures retained beside them. The initial Lean observation attempted
to print a carrier without a `Repr` instance and failed; the successful
rerun serializes its constructors explicitly. This finding is not repaired
in the FLT checkpoint and takes priority over cosmetic execution-marker work.

### September 20, 12:20 UTC — total SF2Prim conversion repaired

The four confirmed failures above now pass. `SF2Prim` keeps its existing
valid-input identity branch and uses an executable private helper for other
finite encodings: reduce the mantissa modulo `2^63`, round the unsigned
integer to binary64, apply the source's clamped exponent scaling, then apply
the sign. The helper constructs its validity evidence from existing closed
rounding operations. Public types and valid-input roundtrip proofs are
unchanged; no new proof hole is added.

The source is Rocq 9.2 Corelib `FloatOps.v:50`, not a declaration owned by
Flocq. An external pinned link and explicit `flocq_local` classification
record that provenance. Corelib states the valid-input roundtrip as the
native-primitive axiom `FloatAxioms.Prim2SF_SF2Prim`; the Lean roundtrip
remains closed by construction. Neither that axiom nor our finite bridge is
a universal cross-prover equivalence proof. `git blame` traces the rejecting
Lean body to `c55f38059d69193210dab282d9e3761297848108`, before the upstream
baseline and earlier Sol audit, rather than to those audit commits.

The new twenty-ninth bridge family `prim_conversion` observes fourteen
columns: input validity, numeric conversion, its proof-carrying projection,
output validity, and the rejecting adapter. It does not sanitize the raw
input before calling the numeric conversion. Shared finite mantissas are
positive, matching Rocq; Lean's additional Nat-zero constructor is excluded.

Verified on library SHA-256
`2df976e002d5e83af940e2f6568f0b6d282b84b8562fc8e9a9a23911c1c92de9`:

- The original four-case bridge run exits with **mismatch** in both Lean
  paths, retained at
  `/private/tmp/floatspec-primitive-conversion-before-20260920/report.json`.
  After the correction, all four cases agree in all three paths and generate four kernel
  equalities in the separate `...-replay-20260920/` run.
- **866** broad cases pass compiled Lean, kernel reduction, and Rocq primitive
  execution, generating **866 kernel equalities**. Seed `843751`, 300 seeded
  supplements, batch 50; **119.578 seconds**. There are 177 valid input
  encodings and **689 invalid raw encodings**; all 866 converted outputs are
  valid, and every invalid input here converts numerically rather than to NaN.
  Receipt: `/private/tmp/floatspec-primitive-conversion-grid-20260920/report.json`.
- A separate deterministic **576-case** replay targets mantissas around
  `2^53`, `2^54`, `2^60`, and `2^63` with both signs and subnormal-scale
  exponents. All three paths and **576 generated kernel equalities** pass in
  **81.139 seconds**. The replay is explicitly provided, not random sampling
  inferred from the report's seed field. Input:
  `/private/tmp/PrimitiveConversionBoundaryGrid20260920.json`; receipt:
  `/private/tmp/floatspec-primitive-conversion-rounding-grid-20260920/report.json`.
  These two grids can overlap; their counts are executions, not a unique-input
  coverage claim. No imported-source edits or library builds overlapped either.
- Paired pure fixtures pass **31 literal cases**, including both signs,
  uint63 wrapping, special values, valid controls, underflow, overflow, and
  huge clamped exponents. Closed examples in each prover distinguish numeric
  conversion from validation and two-stage rounding from one-shot rounding.
  All three printed Lean axiom sets have no sorry. Receipts:
  `/private/tmp/floatspec-primitive-conversion-pure-lean-v2-20260920.log` and
  `/private/tmp/floatspec-primitive-conversion-pure-rocq-20260920.log`.
- The full core harness passes **63 tests in 266.212 seconds**. Three new
  deliberately wrong conversion implementations—reject invalid inputs, skip
  uint63 wrapping, and collapse two rounding stages—are detected in both
  Lean paths while validity/adapter columns stay unchanged.
  Receipt: `/private/tmp/floatspec-primitive-conversion-full-harness-20260920.log`.
- The full macOS Lean 4.34 library/test/executable build passes **6,216 jobs**,
  with complete clean LSP diagnostics for production, fixture, and demo.
  Fresh metadata validates **218 anchors**; compiled trust checks **13,534
  declarations in 58 modules**, exactly four unchanged named debts, and no
  unexpected axioms, unsafe definitions, or runtime overrides. Receipts use
  the same `/private/tmp/floatspec-primitive-conversion-` prefix with
  `all-targets-20260920.log`, `anchors-20260920.log`, and `trust-20260920.json`.
  Generated status is unchanged and the combined runner passes shell syntax
  checking.
- The linear introduction now has a **seventh runnable example**, printing
  both the corrected `1.5` conversion and the exact one-subnormal-unit
  double-rounding difference. It passes its kernel assertion and compiled
  checks: `/private/tmp/floatspec-primitive-conversion-guided-demo-20260920.log`.

The first Lean fixture attempt lacked local binary64 precision instances;
that failure included elaborator-generated sorry errors and is not a passing
proof receipt. Adding the explicit local instances makes all three proofs
close. A targeted harness attempt overlapped the broad rebuild and failed on
a temporarily missing `BitsExecution.olean`; it remains an error at
`...-harness-targeted-20260920.log`. The complete serial harness rerun above
is the passing receipt. The earlier observation-printer and namespace-probe
failures also remain available.

This changes the total raw conversion contract, not the behavior of already
valid binary64 values. The fresh counterexamples and the documented two-stage
algorithm correct a source mismatch; they do not certify the whole port.

### September 20, 12:43 UTC — primitive execution checkpoint; broad grid running

Removed only `noncomputable` from 33 definitions and four arithmetic instances
in `IEEE754/PrimFloat.lean`. No body, type, proof, or source-conversion stage
changes. The fresh baseline
`/private/tmp/PrimitiveExecutionClients-before-c4f0d85f-20260920.out`
records 37 `dependsOnNoncomputable` failures; the new permanent
`PrimitiveExecution.lean/.v` fixtures pass all 37 literal observations.
Three decomposition exponents and the raw-versus-canonical square of 1.5
are checked separately. Printed Lean axiom sets contain no sorry.

New bridge families `prim_arithmetic`, `prim_helpers`, and `prim_round`
have 70, 68, and 16 columns respectively. They call the actual public
primitive-specialized entry points, and arithmetic notation independently.
The raw group runs before conversion; the other groups use total numeric
`SF2Prim` and its proof-carrying projection. Finite shared mantissas are
positive, uint63 inputs are range checked, all five modes are generated,
and the auxiliary rounder admits signed integers exactly as the source does.
Raw addition's random exponents are bounded for test resource use, not by
silently adding a mathematical precondition.

Completed receipts on library SHA-256
`4ad5cb5325f15839c048fc2655e483f084a2ba395d2c556269e5c56144b35ba3`:

- macOS arm64 Lean 4.34 full library/test/executable build: **6,216 jobs**.
  `/private/tmp/floatspec-primitive-execution-all-targets-20260920.log`.
- Pure Lean and Rocq literal fixtures: passing logs
  `...-pure-lean-v3-20260920.log` and `...-pure-rocq-v2-20260920.log`
  under the same prefix. The initial 37-entry fixtures also passed before
  adding the explanatory multiplication example.
- A six-case three-family bridge probe passes both Lean paths, Rocq, and six
  generated kernel equalities:
  `/private/tmp/floatspec-primitive-execution-probe-20260920/report.json`.
- Full core harness: **67 tests in 333.556 seconds**,
  `...-full-harness-20260920.log`. Fourteen independent API/exponent
  mutations are detected in both Lean paths while the other columns remain
  unchanged. Restoring a noncomputable client causes the executable fixture
  to fail. The four targeted new tests separately passed in 45.346 seconds.
- Compiled trust: **13,534 source declarations / 58 modules / four unchanged
  named debts**, no unexpected axioms, unsafe definitions, or runtime
  overrides. `...-trust-20260920.json` and matching log. This used
  `--skip-build` after the successful current full build.
- **218 source anchors** checked against pinned Flocq using metadata freshly
  exported from that build, `...-source-metadata-20260920.json` and
  `...-anchors-20260920.log`. The validator's supplied-manifest mode does
  not itself establish freshness; the preceding full build/export does.
  Complete clean LSP diagnostics for production and fixture, shell syntax,
  and `git diff --check` also pass.

**Still running, not a passing receipt:** the wider **4,970-case** grid,
seed `844763`, 500 seeded supplements per new family, batches of 25:
`/private/tmp/floatspec-primitive-execution-grid-20260920/report.json`.
Imported library sources and the bridge are frozen for this run.
Do not count its planned cases as passed until its final status and generated
kernel-equality count have been checked. The checkpoint can be reviewed while
this larger verification continues.

One fixture revision failed because dotted constructor notation lacked enough
type context inside a compiled Boolean expression. That failure is preserved
in `...-pure-lean-v2-20260920.log`; fully qualifying the constructor makes
the v3 fixture pass. The initial helper CLI lookup used an obsolete script
name and failed; no validation was inferred from that attempt.

#### Next confirmed interface finding: predicate witness constructors

Pinned `Round_pred.v:51,78` returns dependent pairs: a real satisfying the
rounding predicate, or a function with its pointwise proof. Both constructors
take `round_pred rnd` as an input. The current Lean exports instead return
bare values/functions, and select zero when no witness exists. Their separate
Hoare specifications cover only the valid-predicate case. This is an interface
fidelity issue, not a counterexample to those conditional specifications.

Two exact source-shaped clients fail in Lean and pass in Rocq:
`/private/tmp/RoundPredicateWitnessClients20260920-lean-before.out` and
`...-rocq-v2.out`. The first Rocq client attempt omitted the `Defs`
qualification and is retained as an error. A scratch proof-carrying repair
passes, with identity-relation examples and an impossible empty relation:
`/private/tmp/RoundPredicateWitnessDraft20260920.lean/.out`.
No production change is applied during the frozen arithmetic run.


### September 20, 12:52 UTC — standalone macOS demo execution

The seven-part guided demo also passes as a standalone **Mach-O arm64**
executable, not only through `lean --run`. The existing source was compiled
with `lean -c`, compiled to an object with the toolchain's `leanc`, and
linked using the successful `floatspec` target's response-file dependencies,
replacing only its no-op Main object with the demo object. All outputs stayed
in `/private/tmp`; no library build or source edit overlapped the frozen grid.

The executable `/private/tmp/GuidedDemoAOT20260920` exits zero and prints all
seven expected examples, including the exact one-subnormal-unit double-rounding
difference. Receipts use `/private/tmp/floatspec-guided-demo-aot-` with
`elaborate-20260920.log`, `cc-20260920.log`, `link-20260920.log`, and
`run-20260920.log`. The generated C, object, and adjusted response file are
retained beside the binary. The first response-file read was truncated and
rejected before linking; chunked reads reproduced all 479,965 source bytes.

Demo source SHA-256:
`4b436c2e1c6909581fb5b8d47ced02f52f27aef8d77c3b242d8c43716deed6d1`.
Executable SHA-256:
`577909200ec5b56658870b96785ea95f849124b08b17136a2bc982b604404f00`.
Generated C SHA-256:
`8c83fcc363c793d1dbc7d50c7ce3d4bffb766f75c8a86f781505ace8cfdbfbc6`.

This confirms the demonstrated cases across the C compiler/linker execution
path, not a universal compiler-correctness theorem. A persistent Lake demo
target is a useful next integration step after the current source snapshot
is unfrozen; the existing `floatspec` main is still a no-op.

### September 20, 13:09 UTC — tested runner repair and stronger execution drafts

The default-sized primitive batch has a reproducible resource failure.
`prim_arithmetic_corpus(844763, 500)[965:1165]` supplies 200 random cases
after the deterministic grid. Requesting one 200-case batch times out during
Lean kernel reduction after 120 seconds, exits one, and records **error /
zero compared cases**, not a partial pass:
`/private/tmp/floatspec-primitive-default-batch-20260920/report.json`.
Input `/private/tmp/PrimitiveDefaultBatch20260920.json` has SHA-256
`162425dfa954b9d9b2ae1f0a36b6bd9a50b60621fc3c5ef033505e236996abff`.

A scratch scheduling repair caps the three heavy primitive families at 25
cases while retaining the requested maximum for other families. It preserves
input order, duplicates, global offsets, and all replay inputs; timeout errors
still propagate without automatic retry. The **same 200 inputs pass all three
execution paths and 200 generated kernel equalities in 529.109 seconds**:
`/private/tmp/floatspec-primitive-capped-batch-draft-20260920/report.json`.
The report records the requested batch size and the cap table. Five scratch
unit tests also pass, including a timeout in a later batch that retains the
completed count but leaves the whole run in error.
Draft code/tests: `/private/tmp/FlocqBatchDraft20260920.py` and
`FlocqBatchTests20260920.py`. These are not yet the production runner.

The primitive mutation suite was independently expanded from 14 to **40**
replacements: one for each of 33 APIs and four arithmetic instances, plus
three standalone decomposition-exponent mutations. Every replacement is
detected in **both** Lean paths, with columns outside its designated result
unchanged. This scratch suite passes in **117.492 seconds**:
`/private/tmp/PrimitiveAllMutations20260920.py` and
`/private/tmp/floatspec-primitive-all-mutations-draft-20260920.log`.

The next native-IEEE bridge improvement is also exercised without changing
the frozen library. The current `modelObservation` marker still prevents a
compiled caller; `...-native-model-client-before-20260920.out` records that
failure. Removing only the marker in a separate namespace makes the same
body execute, with a closed universal `rfl` equality to the current model.
There is no algorithm rewrite or extra proof debt.

A scratch four-path bridge then compares native FFI, that compiled model
body, the original kernel model, and pinned Rocq on **522 binary64 words**,
seed `845791`. All comparisons and **522 generated kernel equalities pass
in 141.354 seconds**:
`/private/tmp/floatspec-native-four-path-draft-20260920/report.json`.
Sixteen exceptional frexp observations are retained; their native fraction
and exponent are explicitly outside the asserted equivalence, while their
decode/successor/predecessor observations and both complete model outputs
are still compared. Draft sources and the retained runner are
`/private/tmp/NativeFourPathDraft20260920.py` and
`NativeFourPathRun20260920.py`.

All these runs use the unchanged library fingerprint
`4ad5cb5325f15839c048fc2655e483f084a2ba395d2c556269e5c56144b35ba3`.
They prepare integration after the **still-running** 4,970-case production
grid; none is a claim that a draft already ships or that the larger grid
has finished. Only documentation changes during that frozen run.

### September 20, 13:37 UTC — completed primitive grid; integrated runner safeguards

The frozen production grid has now completed successfully: **4,970 cases**,
all compared in kernel Lean, compiled Lean, and pinned Rocq, with **4,970
generated Lean kernel equalities**, zero mismatches, in **3,358.485 seconds**.
Seed `844763` gives 1,465 `prim_arithmetic`, 1,325 `prim_helpers`, and 2,180
`prim_round` cases. Report and retained inputs:
`/private/tmp/floatspec-primitive-execution-grid-20260920/report.json`.
The source fingerprint remained
`4ad5cb5325f15839c048fc2655e483f084a2ba395d2c556269e5c56144b35ba3`.
The recorded launch HEAD is `c4f0d85f` with then-uncommitted primitive changes;
those exact library changes were subsequently committed as `e18434ad`.
The fingerprint, not the launch commit alone, identifies the executed source.

The tested batch-cap repair now ships in `scripts/flocq_bridge.py`. Batches
are homogeneous and preserve original ordering, duplicates, and indices.
Only the three heavyweight primitive families have a 25-case cap; other
families retain the requested maximum. The report includes that maximum and
the cap table. **29 runner/parser/batching tests pass**, including explicit
later-batch timeout handling: completed counts are retained, status is error.
Receipt: `/private/tmp/floatspec-primitive-batch-unit-integrated-20260920.log`.

A production mixed-family replay requests batch size 200 and executes two
lightweight cases around 26 saved random primitive cases. It passes **28/28
comparisons, compiled observations, and generated kernel equalities in
89.819 seconds**, using batches of 1, 25, 1, and 1:
`/private/tmp/floatspec-primitive-mixed-batch-integrated-20260920/report.json`.
This checks the actual driver and global indices, not merely the batch helper.
The earlier 200-case timeout remains a recorded error; the exact complete
200-case scratch rerun described above remains separate evidence.

The production mutation suite now covers **40** independent result changes:
all 33 executable APIs, all four arithmetic instances, and three returned
decomposition exponents. All are detected in both Lean paths; unaffected
result columns remain unchanged. The integrated test passes in **115.133
seconds**:
`/private/tmp/floatspec-primitive-all-mutations-integrated-20260920.log`.
The full harness has five additional unit tests (72 total), but this
checkpoint does not claim that all 72 have been rerun together yet.

No library source or configuration changed during these runs. A separate
1,224-pair native-arithmetic four-path draft is still running; its partial
output is not counted as a completed result. Proof debts remain unchanged.

### September 20, 13:44 UTC — source-shaped proof-carrying rounding constructors

Pinned `Core/Round_pred.v:51,78` takes `round_pred rnd` and returns a dependent
value/function paired with its predicate proof. The previous Lean definitions
omitted that input and returned a bare real/function, selecting zero if no
witness existed. Two source-shaped clients compile in Rocq but fail against
the old Lean interface. This is a contract mismatch, not a counterexample to
the former conditional correctness theorem.

`round_val_of_pred` now returns `{f : ℝ // rnd x f}` and
`round_fun_of_pred` returns `{f : ℝ → ℝ // ∀ x, rnd x (f x)}`. Both require
the source predicate proof. Their two `_spec` adapters are direct projections
of carried proofs, explicitly classified as local helpers; the constructors
have pinned source anchors. No other production callers existed. Classical
choice remains genuinely noncomputable here: this is a mathematical witness
interface, not the executable integer algorithm layer.

The paired `SourcePremiseContracts` fixtures include dependent clients,
identity-value/function examples, and rejection of an empty relation. Two
additional closed Lean theorems universally preserve the old selected value
and function for every valid input. Their five printed axiom lists contain
only `propext`, `Classical.choice`, and `Quot.sound`, not `sorryAx`.

Verification on Lean 4.34.0/macOS arm64:

- Full `FloatSpecLib FloatSpecTests floatspec` build passes **6,216 jobs**:
  `/private/tmp/floatspec-rounding-witness-full-build-20260920.log`.
- LSP diagnostics complete with zero errors for both changed Lean files.
- Paired Rocq fixture passes with pinned Flocq and Rocq 9.2:
  `/private/tmp/floatspec-rounding-witness-rocq-v2-20260920.log`.
  The first invocation used a mismatched output basename and failed before
  compiling; it is retained as an invocation error, not a test pass.
- New theorem axiom receipt:
  `/private/tmp/floatspec-rounding-witness-axioms-20260920.log`.
- Fresh post-build source metadata validates **220** pinned anchors; compiled
  trust checks **13,537 declarations / 58 source modules**, with precisely the
  same four manifest-recorded direct/transitive debts. Reports use the
  `/private/tmp/floatspec-rounding-witness-` prefix and suffixes
  `source-metadata-20260920.json`, `anchors-20260920.log`, `trust-20260920.json`.
- Generated textual status is unchanged: four sorries, no new placeholder
  findings. `git diff --check` passes.

This library snapshot's SHA-256 is
`b77ac977532953f24013c4f31209713e1e3f638cebfc4d9a1bacd25793d41d85`.
No new proof debt was introduced. The source-interface comparison and closed
Lean preservation theorems do not assert whole-library cross-language equality.

Before changing that library snapshot, the separate four-path native arithmetic
draft finished **1,224 pairs**, seed `846811`, with zero mismatches and **1,224
compiled-model observations plus 1,224 generated kernel equalities** in
**1,036.241 seconds**:
`/private/tmp/floatspec-native-arithmetic-four-path-draft-20260920/report.json`.
Its four paths are native Lean FFI, an executable copy of the unchanged model
body, the original kernel model, and pinned Rocq. A universal `rfl` theorem
identifies that copied body with the actual model. It uses the earlier frozen
`4ad5cb53…` fingerprint, not the new rounding-constructor snapshot. Persistent
four-path integration is still pending.

### September 20, 13:52 UTC — unrestricted FLX unit laws and explicit boundary meaning

Compiled pinned Flocq `ulp_FLX_1` and `succ_FLX_1` (`Core/FLX.v:240,246`)
have no positive-precision premise. Their former Lean counterparts added
`Prec_gt_0 prec`, a redundant radix precondition, and an `Id` triple around
the pure result. Source-shaped arbitrary-precision clients therefore compiled
in Rocq but failed to synthesize the extra Lean precision instance.

Both Lean laws now state direct equalities under the existing `ValidRadix`
typeclass, for any integer precision. Their proofs are closed; the two callers
in `Prop/Div_sqrt_error.lean` now consume those equalities directly. Pinned
source anchors were added. Paired clients and four premise guards reject
either `Prec_gt_0` or a hidden legacy positivity `Fact` on these laws.

Both provers prove `ulp 1 = 2` / `succ 1 = 3` at binary precision zero, and
`ulp 1 = 4` / `succ 1 = 5` at precision -1. These concern total mathematical
definitions, not adjacent values in a valid format. Positive precision remains
required for genuinely restricted results such as `negligible_exp_FLX` and
the ULP-at-zero theorem. Two obsolete comments claiming a simplified global
`none`/zero-ULP model were corrected to describe the actual definitions.

Verification:

- Full macOS Lean 4.34 build passes **6,216 jobs**; paired Rocq fixture passes.
  Logs: `/private/tmp/floatspec-flx-unit-full-build-20260920.log` and
  `/private/tmp/floatspec-flx-unit-rocq-20260920.log`.
- Changed FLX laws and the production caller have complete zero-error LSP
  diagnostics. The combined client file's LSP check timed out, then reported
  unavailable dependency diagnostics; neither attempt is counted as clean.
  The full build and a separate direct client typecheck both pass, the latter
  with empty output in `...-flx-unit-direct-clients-20260920.log`.
- Printed axioms for both laws and the boundary theorem contain only
  `propext`, `Classical.choice`, `Quot.sound`:
  `/private/tmp/floatspec-flx-unit-axioms-20260920.log`.
- Fresh metadata validates **222** anchors. Compiled trust checks **13,537
  declarations / 58 modules**, precisely four unchanged manifest-only debts.
  Metadata, anchor receipt, and trust reports use the
  `/private/tmp/floatspec-flx-unit-` prefix. Source SHA-256:
  `df96665572a99065e3c61087085cb2bd159498862bbf9e9ec5252c202cae0375`.
- There are now **90 positive premise guards**, plus five deliberate negative
  guard examples and one guard self-test. Generated textual status, shell
  syntax, and whitespace checks pass; no new proof debt.

A preliminary whole-file scratch copy was accidentally truncated, and a second
attempt lacked the package's style-linter options. Those failed drafts are not
passes. The complete copy with the actual package-style options passed with
empty output before production integration (`FLXWholeModuleUnitDraft20260920-v4.out`).
Neither this type repair nor its finite examples certify the remaining FLX
theorems or the rest of the port.

### September 20, 13:56 UTC — persistent four-path native bridges and Lake-built demo

Both native test-model adapters now compile at their actual exported names.
Fresh clients failed with `dependsOnNoncomputable` before removing only the
two `noncomputable` markers; the identical clients compile afterward. Their
bodies, types, and logical proofs are unchanged. The persistent IEEE and
arithmetic bridges now require four complete observations: native Lean FFI,
compiled logical Lean model, kernel-reduced logical model, and pinned Rocq.
They retain each stream and count compiled-model cases separately.

All model fields are compared with Rocq, including exceptional frexp outputs.
Only the documented native frexp nonzero/finite boundary limits the native
comparison. Kernel/Rocq agreeing results still produce individual kernel
equalities; a separate compiled-only discrepancy remains an overall mismatch
even when those equalities pass. Missing paths are errors, not a silent
downgrade. Independent live mutations corrupt native and compiled paths and
must retain replay inputs. No new oracle arithmetic was implemented.

The seven-part `GuidedDemo.lean` source now has a real `floatspec_demo` Lake
target. `lake exe floatspec_demo` runs a linked native executable with all
seven kernel-asserted/runtime-checked examples. The combined three-loop shell
runner also invokes it. The unrelated legacy `floatspec` target remains a
no-op smoke test. Guides now lead with the useful executable command.

Verification on macOS arm64/Lean 4.34.0:

- `lake build FloatSpecLib FloatSpecTests floatspec floatspec_demo` passes
  **6,219 jobs**: `/private/tmp/floatspec-four-path-demo-build-20260920.log`.
- `lake exe floatspec_demo` exits zero; all seven examples pass:
  `/private/tmp/floatspec-lake-demo-run-20260920.log`.
- The **19-test** native bridge harness passes in **43.458 seconds**, including
  all live native/compiled-only mutations and timeout/interruption tests:
  `/private/tmp/floatspec-four-path-live-harness-20260920.log`.
  Its 12 unit tests also passed before the live run; they are not 12 extra
  independent tests beyond the 19.
- Both changed Lean adapters have complete zero-error LSP diagnostics.
  Before/after client logs use `/private/tmp/floatspec-native-model-integrated-`
  and `floatspec-native-arithmetic-model-integrated-`, followed by
  `before-20260920.log` / `after-20260920.log`.
- Compiled trust remains **13,537 declarations / 58 modules / four unchanged
  manifest debts**. Fresh source metadata validates **222** pinned anchors.
  Reports use `/private/tmp/floatspec-four-path-` with
  `trust-20260920.json`, `source-metadata-20260920.json`, `anchors-20260920.log`.
- Shell syntax and `git diff --check` pass.

This snapshot's Lean/configuration SHA-256 is
`2cb288c3347dc66b2324b2ac6ad02ebfa84bd839affbde4d811789d6b7f40958`.
The demo binary is Mach-O arm64 with SHA-256
`8b82f999ea2793484c4d9e0552cf378d9bb6faf0c2234af817046fcca7ff46ce`;
its unchanged source hash is
`4b436c2e1c6909581fb5b8d47ced02f52f27aef8d77c3b242d8c43716deed6d1`.

The earlier 522-word and 1,224-pair scratch runs are separate evidence on the
previous snapshot. The next all-family combined run is still pending here;
neither launching it nor these targeted successes constitute a whole-port
semantic-equivalence proof. Hosted-CI cache/toolchain mismatch remains separate.

### September 20, 14:12 UTC — readable current checkpoint and paired double-rounding clients

The fresh combined three-loop run launched at 13:57:25 UTC on clean commit
`2282a69b`, with frozen Lean/configuration fingerprint
`2cb288c3347dc66b2324b2ac6ad02ebfa84bd839affbde4d811789d6b7f40958`.
It is **running, not passed**. Its core corpus has **48,614 cases**, seed
`848933`; native sampling is 200 and arithmetic sampling is 100.
Fresh source/trust gates and their harnesses pass. The pure Rocq arithmetic,
bits, order, premise/contract, rounding-oracle suites pass; the Lean fixed
fixtures and seven-part demo also complete before the core bridge.
The later native/specialized bridges and final aggregate result remain pending.

Log: `/private/tmp/floatspec-full-three-loop-2282a69b-20260920.log`.
Core artifacts:
`/private/var/folders/gn/1hqqc7pn3nz5s_p0dxnn9h300000gp/T/floatspec-bridge-3r49wz16`.
Library, configuration, fixtures, and test tools remain unchanged during the
run. This checkpoint changes explanation only.

While frozen, paired scratch clients reinforced the existing bounded
double-rounding review: nine source-body equalities by reflexivity and six
theorem clients with source-shaped premises. Both files now compile;
the six Lean client axiom lists contain only `propext`, `Classical.choice`,
and `Quot.sound`. This adds executable interface evidence, not a new review
of every internal proof in the large module.

Sources: `/private/tmp/DoubleRoundingSourceClients20260920.lean` and `.v`.
Successful receipts: `-lean-v2.out` and `-rocq-v3.out` beside them.
The first Lean draft had ambiguous compatibility aliases. The first Rocq
draft had an invalid import form, the next needed an explicit radix-to-integer
coercion; those failed attempts are retained and not counted as passes.
The definition comparison's division clause was also aligned with the exact
source premise order before its reflexivity check.

The reading guide now leads with one current checkpoint rather than a
chronological mix of obsolete counts. The focused ledger records the
proof-carrying constructors, unrestricted FLX laws, and all 40 primitive
mutations. Earlier smaller counts remain explicitly historical.

### September 20, 14:31 UTC — preserve failures and make the broad corpus practical

The 13:57 combined run was deliberately interrupted after an avoidable
scheduling problem was measured. Homogeneous batching fragmented the
48,614-case corpus into **2,502 batches**, including **1,653 singletons**.
The parent exits **130** and the retained core report records
`status: error`, `KeyboardInterrupt`, **1,755 compared/compiled cases**
and **1,754 completed bootstrap proofs**, after **1,150.071 seconds**.
It is not a passed aggregate run; the differing counters correctly preserve
the interruption during the next bootstrap proof. Its processes stopped
before any production source/tool changes.

Ordinary families can now share a batch; each row still has its own exact
operation-specific width check. The three expensive primitive families remain
homogeneous and capped at 25. No case is reordered, deduplicated, or dropped.
The identical corpus now uses **378 batches**, retaining the same seed and
inputs. New unit/driver tests check exact global offsets, input preservation,
caps, family boundaries, and mixed light-family execution.

Verification on the unchanged `2cb288c3…` library snapshot:

- All **75 existing-plus-batching harness tests pass**, including the live
  prover mutations, in **385.059 seconds**:
  `/private/tmp/floatspec-efficient-batch-harness-v2-20260920.log`.
- A newly permanent 76th live regression separately passes: one mixed batch
  with **87 cases / all 29 ordinary families**, all three execution paths,
  and all 87 generated kernel equalities.
  Receipt: `/private/tmp/floatspec-mixed-light-live-regression-20260920.log`.
  The 76th test was added after the 75-test run; these are separate receipts.
- The actual integrated CLI replay also passes the same 87 cases in
  **6.160 seconds**:
  `/private/tmp/floatspec-mixed-light-batch-integrated-20260920/report.json`.
  Its preliminary scratch pilot passed in 6.734 seconds, separately.
- `git diff --check` passes; no Lean/configuration files changed.

The first harness invocation used a module-import form incompatible with
the scripts' import layout and failed before testing. Its log is retained as
`floatspec-efficient-batch-harness-20260920.log`, not a pass.
The next complete three-loop run will restart the entire corpus after the
separately scratch-verified parity/symmetry contract repairs are integrated;
no completed prefix is silently promoted into a full run.

### September 20, 14:38 UTC — six parity/symmetry source interfaces repaired

Compiled pinned types exposed six additional section-premise mismatches.
The two `DN_UP_parity_*_prop` definitions take no `Valid_exp` in Flocq.
`DN_UP_parity_aux` and `round_NE_opp` need neither `Valid_exp` nor
`Exists_NE`; `round_NE_abs` needs validity but not `Exists_NE`;
`round_odd_opp` needs no exponent-validity premise. Lean formerly required
all the extra instances. Source-shaped clients failed against those types.

The six public signatures and one private symmetry helper now have the
source premise boundaries. Every production proof body is unchanged and
closed. Six new pinned anchors identify the inspected exports; actual
parity-existence/correctness theorems retain their stronger hypotheses.
The compiled-premise guard now accepts multiple named arguments and is tested
against deliberate implicit and explicit `Exists_NE beta fexp` leaks, plus
an independent-exponent control. There are **98 production premise guards**,
**seven expected-negative examples**, and **two guard self-tests**.

Paired clients also prove a useful boundary: binary FLX precision one does
not satisfy the source's `Exists_NE` condition, while its concrete
nearest-even rounding still commutes with negation. This shows an actual
positive-precision case excluded by the old symmetry signature. It does not
claim that the class characterizes nearest-even totality in both directions.

Verification on macOS arm64 / Lean 4.34.0:

- Full `FloatSpecLib FloatSpecTests floatspec floatspec_demo` build passes
  **6,219 jobs**: `/private/tmp/floatspec-parity-full-build-20260920.log`.
  The earlier targeted dependency build passes 3,060 jobs.
- Both production modules and the combined premise fixture have complete
  zero-error LSP diagnostics. The old standalone clients now compile without
  errors (`RoundNEUnrestrictedClients20260920-after.out` and
  `RoundOddUnrestrictedClients20260920-after.out` in `/private/tmp`).
- The complete paired Rocq premise fixture passes:
  `/private/tmp/floatspec-parity-source-rocq-20260920.log`.
- Ten printed source/client axiom lists contain only `propext`,
  `Classical.choice`, and `Quot.sound`:
  `/private/tmp/floatspec-parity-axioms-20260920.log`.
- Compiled trust remains **13,537 declarations / 58 modules / four unchanged
  manifest-only debts**. Source metadata was freshly exported after the
  successful build; validation of that saved metadata checks **228 anchors**.
  Reports use `/private/tmp/floatspec-parity-` with suffixes
  `trust-20260920.json`, `source-metadata-20260920.json`, and
  `anchors-20260920.log`. The validator's supplied-manifest mode does not
  itself establish freshness; the preceding export/build does.
- The real seven-part Lake demo reruns successfully:
  `/private/tmp/floatspec-parity-demo-20260920.log`.
  Generated textual status is unchanged; shell syntax and whitespace checks pass.

Lean/configuration SHA-256:
`32ec11b5b0ac7fb6cba5d58635307df2857568f7228c9554e8343d498305dfbf`.
Scratch whole-module proofs passed before integration. Early boundary drafts
failed on a missing FLX import (the scratch copy cannot import its own
downstream module), missing `Lia`, and a section-local real-number scope;
those failed receipts remain, and the successful final scratch receipts are
`RoundNEWholeUnrestricted20260920-v6.out`,
`RoundNEUnrestrictedClients20260920-rocq-v5.out`, and
`RoundOddWholeUnrestricted20260920.out`.
No new proof admission or arithmetic algorithm change was introduced.
The complete differential rerun remains pending until the new snapshot is
committed and frozen; earlier aggregate runs are not relabeled as current.

### September 20, 14:50 UTC — current frozen rerun and Pff probe

The complete runner restarted at **14:38:51 UTC** on pushed commit
`5a6d16df`, with Lean/configuration fingerprint `32ec11b5…` recorded above.
The source/trust gates, pure Rocq suites, pure Lean suites, and native demo
have passed. The core differential stage is still running; it is not yet
an aggregate success. It uses seed `848933`, 100 random samples per family,
and the unchanged ordered **48,614-case** corpus, now in 378 batches.

Current log: `/private/tmp/floatspec-full-three-loop-5a6d16df-20260920.log`.
Core artifacts:
`/private/var/folders/gn/1hqqc7pn3nz5s_p0dxnn9h300000gp/T/floatspec-bridge-1vtmvy__`.
Production sources, configuration, and verification tooling remain frozen
while this run executes. Documentation changes do not alter its fingerprint.

In parallel, a scratch-only Pff source-facade probe is testing digit count,
shift, addition, subtraction, normalization, negation, and absolute value
against pinned Pff, including radix zero, one, and negative values and
zero precision where the exported functions have no excluding premise.
The first probe failed before comparison because its generated Lean header
used unsupported namespace-alias syntax. The error report is retained at
`/private/tmp/floatspec-pff-source-probe-20260920/report.json`; it is not a
pass. A corrected-header run has a separate `-v2-` artifact directory.
Neither the probe nor its result certifies the legacy module or changes
the port's numerical definitions.

### September 20, 15:02 UTC — Pff executable slice and a separate radix gap

The scratch Pff source-facade probe completes **1,452 cases**, seed `849917`,
with compiled Lean, kernel Lean, pinned Rocq, and **1,452 generated kernel
equalities**. Fourteen columns observe digit/Fdigit, shift, addition,
subtraction, normalization, negation, and absolute mantissa. Inputs include
radices -16 through 16, zero/one/negative radices, zero precision, and random
mantissas up to 192 bits; the reference's exported domains are preserved.
Report: `/private/tmp/floatspec-pff-source-probe-v4-20260920/report.json`.
This uses the unchanged `32ec11b5…` library snapshot, not copied Lean APIs.

An independent exact-rational Python oracle checks **14,078 assertions**
across those same 1,452 actual compiled observations: shift/add/subtract/
normalization value preservation at nonzero radix, negation, positive-radix
absolute value, division-based digit counts at radix at least two, and the
zero-normalization exponent. These are finite oracle checks, not new Lean
theorems. The harness also detects **all 14 independently corrupted columns**
in both Lean execution paths, checking that the remaining columns are equal.
Report: `/private/tmp/floatspec-pff-probe-harness-20260920/report.json`.

The first three probe attempts remain errors: unsupported namespace alias,
ambiguous root/source names, and truncated pretty-printer output respectively.
The strict parser correctly rejects that truncation. Version four uses fully
qualified source names and the normal bridge's full-output settings.

A separate paired typed probe confirms a compatibility-interface gap.
The root `FNeven`, `FNodd`, `FNSucc`, and `FNPred` ignore their real-valued
radix argument and normalize at the independent Core index. Pinned Pff's
four exports instead use their single explicit integer radix, with no
radix-validity premise. With bound `(vNum=9,dExp=10)`, precision two, and
explicit radix three:

| Observation | Pinned Pff | Old wrapper indexed by two |
|---|---|---|
| Normalized successor of `(1,0)` | `(4,-1)` | `(3,-1)` |
| Normalized predecessor of `(2,0)` | `(5,-1)` | `(8,-1)` |
| Normalized parity of `(1,0)` | odd, not even | even, not odd |

The bound is a valid base-3 precision bound; it is not a base-2 precision
bound. These are definition-domain counterexamples to treating the wrapper's
extra argument as operational, not counterexamples to conditional neighbor
theorems. Successful receipts are
`/private/tmp/PffIgnoredRadixProbe20260920-lean.out` and
`/private/tmp/PffIgnoredRadixProbe20260920-rocq-v3.out`.

An eight-definition explicit-radix source-facade candidate and six boundary
assertions typecheck in scratch, with two closed carrier-adapter proofs for
the unnormalized successor/predecessor:
`/private/tmp/PffSourceNeighborsDraft20260920-v6.out`.
This candidate is **not yet integrated**; production remains frozen for the
broad three-loop run. Earlier draft proof attempts and the unsupported
scratch-file LSP query are errors, with direct `lake env lean` used as the
fallback. No global normalization equivalence or complete Pff audit is claimed.

### September 20, 15:30 UTC — repair Pff's total logarithm convention

Independent inspection of the installed Rocq Stdlib `Reals/Rpower.v:216`
showed that `ln x` is zero at nonpositive inputs, unlike Lean's absolute-value
extension. Pinned `Pff.RND_Min_Pos` uses that function without exporting a
radix-positivity premise. Paired closed probes established a concrete mismatch
at `(bound=(4,0), radix=-2, precision=2, input=2)`: source `(-4,-1)`, old Lean
`(2,0)`. Both represent two, but their source records differ.

The source facade now has `rocqLn`, explicitly classified as a Stdlib boundary,
and uses it in `RND_Min_Pos`, which receives a pinned Flocq anchor. The paired
permanent `PffLogTotality` fixtures prove the source results for inputs two and
minus two. A closed Lean theorem proves universal preservation of the old
formula for every positive integer radix, natural precision, bound, and real
input. All four printed regression axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`. Existing positive-radix fixtures remain
closed after adding the helper to their unfolding lists.

To preserve the original frozen run, changes moved to a new isolated worktree
`/Users/alokbeniwal/.codex/worktrees/astra-pff-source-boundary/FloatSpec`, branch
`codex/astra-pff-source-boundary`, based on `2e3ea2d1`. Its `.lake` is an APFS
copy, not a symlink or hard-linked build directory. The original continuation
worktree and its **48,614-case** run remain unchanged.

Verification on this new slice:

- Full build passes **6,220 jobs**, both before and after adding printed axiom
  checks: `/private/tmp/floatspec-pff-log-full-build-v2-20260920.log`.
- Source facade, old totality fixture, and new totality fixture have complete,
  zero-error LSP diagnostics. Each new Lean proof was checked individually.
- Both permanent Rocq counterexamples pass:
  `/private/tmp/floatspec-pff-log-rocq-v2-20260920.log`.
- Compiled trust: **13,538 source declarations / 58 modules / four unchanged
  manifest-only debts**. Freshly exported metadata validates **229 anchors**.
  Receipts: `/private/tmp/floatspec-pff-log-trust-20260920.json`,
  `floatspec-pff-log-source-metadata-20260920.json`, and
  `floatspec-pff-log-anchors-20260920.log` in the same directory.
- The real Lake demo passes again. Shell syntax, generated status, and
  whitespace checks pass; no new proof debt was added.

New Lean/configuration fingerprint:
`f5f06e6603af9bd059443ee574dd4e2ae5e73edc29ece56eca870e517854bd17`.
The broad run on the earlier `32ec11b5…` snapshot is still running, not yet
passed and not relabeled as checking this semantic change.

Scratch Pff native work is separate: a full copied Pff module compiles after
removing 18 `noncomputable` markers across root/source APIs, with bodies and
types unchanged, and executes 24 entry-point checks. The expanded 56-column,
2,772-case candidate run stopped after 2,600 compared/proved cases because
Rocq emitted a large-natural-literal warning. Its status is **error**, not
pass. A new run encodes natural arguments via binary `Z.to_nat` expressions;
it preserves every input and keeps stderr checking enabled. It remains
in progress, and none of those native/interface candidates is integrated yet.

### September 20, 16:01 UTC — integrated Pff native/source boundary and three-path profile

The eight explicit-radix neighbor/parity definitions are now integrated in
`Pff.Source`, with pinned source anchors and two closed raw-neighbor carrier
bridges. Older normalized wrappers are explicitly classified as indexed
compatibility APIs. The source facade opts into the source-definition
linter, and all its public definitions are source-linked or explicitly local.
Fifteen root and three pre-existing facade definitions become computable;
their types and bodies are unchanged. The same eighteen-entry client that
failed before this change now executes every entry point successfully.

The permanent paired `PffExecution` fixtures check all eighteen APIs and the
base-three/base-two neighbor distinction, with source parity. Lean's three
regression theorems and two carrier-bridge theorems have printed axiom lists
without `sorryAx`. `PffWalkthrough.lean` prints the records and explains the
different operational radices linearly, with failing runtime assertions.
The combined runner includes both fixtures, the walkthrough, and the new
Pff differential profile and harness.

Verified at Lean/configuration SHA-256
`ae6a6458b65f1742274a98ba120e9406a638df9d7f6f5289804abad503daacb9`:

- Full macOS Lean 4.34 build: **6,221 jobs**, exit zero, receipt
  `/private/tmp/floatspec-pff-native-full-build-20260920.log`.
- Integrated three-path Pff profile: **2,772 / 2,772 compared, compiled,
  and bootstrapped kernel cases**, seed **850021**, 56 columns, 488.697 seconds.
  All **45,368** independent exact-rational assertions pass, including
  **3,510** canonical-neighbor assertions under explicit source premises.
  Full inputs, source hash, generated programs, outputs and report:
  `/private/tmp/floatspec-pff-integrated-20260920/`.
- All **16** Pff harness tests pass in 23.798 seconds, including live
  mutations in all 56 columns of both Lean paths, compiled-only mutation
  with a persisted mismatch/replay, wrong bootstrap expectations,
  matching-wrong-result oracle failure, malformed inputs, timeout and
  interruption behavior, and restoration of every shared-runner binding.
  Receipt: `/private/tmp/floatspec-pff-harness-live-v2-20260920.log`.
- Core harness: **32 non-live tests pass**, 44 live tests explicitly skipped
  in this invocation, not counted as passes. The frozen broad runner will
  execute the live suite separately. Receipt:
  `/private/tmp/floatspec-pff-core-harness-20260920.log`.
- Compiled trust: **13,553 declarations / 58 modules / four unchanged
  manifest-only proof debts**, no new axioms or runtime overrides.
  Freshly exported source metadata validates **262 pinned anchors**.
  Receipts: `/private/tmp/floatspec-pff-native-trust-20260920.json`,
  `floatspec-pff-native-source-metadata-20260920.json`, and
  `floatspec-pff-native-anchors-20260920.log` in the same directory.
- Paired fixtures, the seven-part Lake demo, the new Pff walkthrough,
  Python compilation, shell syntax and whitespace checks pass. Source
  facade, finite Lean fixture and walkthrough have complete zero-error LSP
  diagnostics. The large root Pff LSP query remained partial; its full
  module and project builds provide the completed fallback verification.

The copied-module candidate is separately retained: its 2,772-case rerun
also passed after the large-natural codec correction. It is not substituted
for the integrated run above. During integration an overlapping Lake module
build encountered an `EACCES` error on a cache-restored read-only artifact;
that failed log is retained as
`/private/tmp/floatspec-pff-native-source-build-20260920.log`.
No cached hardlinks were chmodded or deleted. Serialized retries and the full
build passed; no overlapping module builds were used for this final snapshot.

The older **48,614-case** broad run remains active on the earlier frozen
`32ec11b5…` source snapshot. It is not yet an aggregate pass and does not
cover these new Pff definitions. The new finite agreement, named bridge
proofs, source anchors, and whole-library source equivalence remain distinct
claims. No complete Pff theorem audit or normalized-carrier equivalence is
claimed.

### September 20, 16:16 UTC — execute auxiliary bounds; separate identity from normalization

Seven more integer-only auxiliary entry points now execute with unchanged
bodies/types: `make_bound`, `bsingle`, `bdouble`, `PFnormalize`,
`pff_compare`, `pff_max`, and `pff_min`. The pre-change native client failed
at all seven and the identical client now returns the expected observations.
Three actual source exports receive pinned anchors; the indexed normalizer
and local numerical helpers are explicitly classified as adapters/local
definitions. A misleading comment claiming lowercase `pff_normalize`
matched normalization was false: it is the identity. Its documentation and
classification are corrected without silently changing a compatibility API.
A closed regression distinguishes identity `(1,0)` from actual normalized
`(4,-2)`. Normality documentation now includes the mantissa requirement.

Verified on source/configuration SHA-256
`383e8d3ec6c31be1bb8fae93b3f04d531acb75274b260fd0c5a19e750b9ad51b`:

- Full macOS Lean 4.34 build passes **6,222 jobs**;
  `/private/tmp/floatspec-pff-aux-full-build-20260920.log`.
- Source-bound/adapter profile passes **2,216** compared, compiled and
  bootstrapped kernel cases, seed **852017**, ten columns, 252.078 seconds,
  with **11,872** independent exact-rational/bound assertions. Complete
  evidence: `/private/tmp/floatspec-pff-aux-integrated-20260920/`.
- The pure Lean oracle passes **70,227** comparison/min/max cases at radices
  two, three and ten. Its 225-case kernel grid, identity counterexample and
  bound literals have printed axiom lists excluding `sorryAx`. Paired Rocq
  bound and normalization fixtures pass. Receipts:
  `/private/tmp/floatspec-pff-aux-lean-20260920.log` and
  `floatspec-pff-aux-rocq-20260920.log`.
- All **eight** auxiliary harness tests pass, including live corruption of
  all ten differential columns, matching-wrong-output rejection, and
  deliberate failure of Lean kernel/runtime and Rocq source-bound oracles.
  Receipt: `/private/tmp/floatspec-pff-aux-harness-v2-20260920.log`.
  The initial harness run failed because it expected different Lean error
  wording; its log is retained. The repaired test also proves the mutated
  finite claim is false, rather than treating any compiler failure as proof
  of a valid negative control.
- Fresh compiled trust is still **13,553 declarations / 58 modules / four
  unchanged manifest-only debts**, with no runtime overrides. Fresh export
  and validation cover **265** pinned anchors. Receipts use prefix
  `/private/tmp/floatspec-pff-aux-{trust,source-metadata,anchors}-20260920`.
- Changed source and finite-test files have complete zero-error LSP
  diagnostics. Python compilation, shell syntax, generated status and
  whitespace checks pass. The runnable seven-part demo passes again.

These results distinguish source exports, explicitly converted compatibility
arguments, and Lean-only exact-value helpers. They do not establish a whole
auxiliary-module source equivalence. The separate older full runner is still
active on its frozen snapshot; its aggregate result remains pending.

### September 20, 16:40 UTC — one-radix signed rounding; paired semantic negative controls

Added four source-facing real-valued definitions: `RND_Max_Pos`, `RND_Min`,
`RND_Max`, and `RND_EvenClosest`. Their bodies were compared directly with
pinned source lines 27523–27641. Every branch shares the same explicit
integer radix; exact upward rounding retains the lower record, inexact uses
its raw successor, negative wrappers exchange positive directions, and the
nearest tie tests the lower mantissa's parity. The old indexed counterparts
are explicitly local compatibility interfaces. Real comparison/logarithm
definitions remain noncomputable; no native-execution claim is made.

Verified source/configuration SHA-256:
`b8e888c0b96594f1e59e0657eab46cf160d504db47e1823b3d64b9a837e3b1c6`.

- Full macOS Lean 4.34 build passes **6,223 jobs**; receipt
  `/private/tmp/floatspec-pff-rounding-full-build-20260920.log`.
- Ten paired closed Lean/Rocq rows pass: four signed/parity halfway cases,
  two strict-distance cases, exact integer, zero, negative radix and zero
  precision. All ten Lean axiom lists exclude `sorryAx`. Receipts:
  `/private/tmp/floatspec-pff-rounding-{lean,rocq}-20260920.log`.
- Both live mutation tests pass: original halfway result accepted,
  nearest-even replaced by downward rejected for a semantic mismatch,
  altered expected result positively proved. Receipt
  `/private/tmp/floatspec-pff-rounding-controls-20260920.log`, 8.634 seconds.
  The controls and paired fixtures are permanent combined-runner stages.
- Complete zero-error LSP diagnostics for the source facade and Lean fixture;
  compiled trust **13,557 declarations / 58 modules / four unchanged debts**;
  fresh metadata export and validation **269 pinned anchors**. Receipts use
  prefix `/private/tmp/floatspec-pff-rounding-{trust,source-metadata,anchors}-20260920`.
- Seven-part executable demo, shell syntax, Python compilation and generated
  status pass. Status counts 96 Lean files, four sorries, no explicit axioms
  or admits. No proof debt was added.

Separately, the frozen `32ec11b5…` broad run completed all **48,614** core
comparisons and generated kernel equalities in 6,122.028 seconds, then its
saved replays and **76-test** live core harness passed. Native stages remain
in progress. This is not yet an aggregate pass and does not cover the newer
Pff definitions above. Exact core artifacts are retained under
`/private/var/folders/gn/1hqqc7pn3nz5s_p0dxnn9h300000gp/T/floatspec-bridge-1vtmvy__`;
the aggregate log is `/private/tmp/floatspec-full-three-loop-5a6d16df-20260920.log`.

### September 20, 16:44 UTC — permanent double-rounding contracts and a separating example

Promoted the previously checked scratch clients into permanent paired
`DoubleRoundingContracts` fixtures: nine literal definition-body equalities
and six clients with the reviewed exported premises. Added a closed paired
example using exponent functions `e - 1` and `e - 3`; the radix-at-least-four
square-root condition holds while the ordinary condition fails. Thus its
one-radix-digit improvement is an observable contract distinction.

Final source/configuration SHA-256:
`81babc5076d5c6222e1a463b5f5ae39feb64d94b1b3e81e755a5bd7d497d5116`.
The **6,224-job** macOS Lean 4.34 build passes; complete LSP diagnostics
have zero errors. Both assistants close the paired fixtures; all six Lean
client axiom lists and the separating example exclude `sorryAx`. Three
live negative controls pass: changing the radix-four offset is rejected by
both assistants, and requiring additional unavailable `Valid_exp` premises
breaks the Lean multiplication client. The original unmutated fixture is
checked before every negative control. Compiled source trust remains
**13,557 declarations / 58 modules / four unchanged debts**. No product
definition, product proof, or source anchor changed in this slice.

Receipts: `/private/tmp/floatspec-double-contract-full-build-v3-20260920.log`,
`floatspec-double-contract-lean-v2-20260920.log`,
`floatspec-double-contract-rocq-v3-20260920.log`,
`floatspec-double-contract-controls-20260920.log` (three tests, 10.514 seconds),
and `floatspec-double-contract-trust-20260920.json` in the same directory.
The first separating-example draft needed explicit Lean beta reduction and
Rocq's `Lia` import; those failed attempts were corrected before verification
and are not passes. Generated status now counts 97 Lean files, still four
sorries and no explicit axioms/admit. Shell/Python/whitespace checks pass.

This protects the bounded source review already documented; it does not
upgrade it into an exhaustive audit of every double-rounding theorem.
The separate frozen broad runner remains active in its native stages.

### September 20, 16:58 UTC — execute model adapters; correct the out-of-domain oracle

Removed only two unnecessary execution markers from `binary32OfModel` and
`binary64OfModel`, keeping bodies/types unchanged and classifying them as
Lean-model adapters. The identical pre-change native client failed at both
entry points; it now executes and returns canonical NaN words. Baseline
receipts: `/private/tmp/NativeAdaptersBaseline20260920-{before,after}.out`.

Running the independent oracle exposed its incorrect wrap-everywhere
assumption. Pinned `Bits.v:77` sets the sign using an integer threshold;
outside `0 <= x < 2^width`, source decoding differs from a UInt conversion.
Direct Rocq evaluation confirmed the same behavior as Lean. The initial
oracle failure is retained in
`/private/tmp/floatspec-native-adapters-invalid-oracle-20260920.log`.
This was a harness/domain error, not a newly discovered port mismatch.
Paired closed regressions now distinguish signed NaN canonicalization,
`2^32 + 1` finite decoding, and signed zero from input `-2^63`.

Verified on source/configuration SHA-256
`129ab2f68a56238920363d578449ca24ba922a101a09e131e038d140c749559b`:

- Integrated three-path profile: **1,140 compared/compiled/generated-kernel
  cases**, seed **854033**, **5,700** independent column assertions,
  **827** out-of-range inputs and **445** distinct source/model routes,
  292.027 seconds. Complete report/corpus/generated proofs:
  `/private/tmp/floatspec-model-adapter-integrated-20260920/`.
- Pure Lean: **60,032 inputs / 300,160 observations**, plus 32 boundary
  inputs checked by kernel reduction. All four named regression axiom lists
  exclude `sorryAx`. Paired Rocq examples pass. Receipts:
  `/private/tmp/floatspec-native-adapters-lean-20260920.log` and
  `floatspec-native-adapters-rocq-v2-20260920.log`.
- All **seven** adapter harness tests pass, including live corruption of
  every column at both widths, matching-wrong-output rejection, and a false
  wrapping bootstrap followed by successful correct bootstrap; 13.547 seconds.
  Receipt: `/private/tmp/floatspec-model-adapter-harness-live-20260920.log`.
  The earlier unit-only invocation explicitly skipped its three live tests.
- Full macOS Lean 4.34 build **6,225 jobs**; fresh compiled trust
  **13,557 declarations / 58 modules / four unchanged debts**; freshly
  exported metadata validates **269** pinned source anchors. Receipts use
  `/private/tmp/floatspec-model-adapter-{full-build,trust,source-metadata,anchors}-20260920`.
- Complete zero-error LSP diagnostics for the changed source and fixture;
  demo, Python compilation, shell syntax, generated status and whitespace
  checks pass. Status: 98 Lean files, four sorries, no explicit axioms/admit.

The profile explicitly states that it has no native float FFI. Its Rocq
mapping applies NaN canonicalization and wrapping only on the corresponding
adapter routes; it does not invent a source export for Lean's logical model.
The first Rocq fixture draft lacked explicit precision/exponent parameters
on `Binary.is_nan`; it failed and was corrected. The first bridge invocation
used an unsupported output flag and exited before testing; only the corrected
invocation above is counted. The frozen broad run has now passed native unary
and arithmetic stages and their harnesses; its remaining stages are active.

### September 20, 17:08 UTC — LPO producers return the source proof-carrying alternatives

Repaired `Raux.LPO_min`, `LPO`, and `LPO_Z` against pinned source lines
2271, 2384 and 2396. Three pre-change typed clients failed with the concrete
`Prop` versus `Type` mismatch: the old names were Hoare properties of
optional values, while the source returns dependent witnesses or universal
nonexistence proofs. The new `PSum` results retain the exact minimum,
membership and negative-branch contracts. Integer construction mirrors the
source's nonnegative-then-negated-natural order. The old optional definitions
are unchanged; their theorem names become explicit `_choice_spec` adapters.
Repository search found no old-name callers requiring migration.

Source/configuration SHA-256:
`74b1ea8a5c19b6e1c4dbc2a91bd7a97b6717ad50a7f55fe03ffe33923b8c4b8c`.

- Full macOS Lean 4.34 build passes **6,226 jobs**; receipt
  `/private/tmp/floatspec-lpo-full-build-20260920.log`.
- The identical three baseline clients now compile. Paired permanent
  fixtures consume all three result types, extract proof-carrying witnesses,
  and cover negative-only and empty predicates. Two closed Lean theorems
  prove that dropping the natural witness proofs recovers the previous
  optional choices. All seven printed client/theorem axiom lists exclude
  `sorryAx`. Receipts: `/private/tmp/LpoSourceBaseline20260920-{before,after}.out`,
  `floatspec-lpo-contract-lean-final-20260920.log`, and
  `floatspec-lpo-contract-rocq-20260920.log`.
- Both live contract controls pass (5.545 seconds): all three former
  property-only results fail the Lean source clients, and Rocq rejects a
  proof-erased optional result. The original fixtures pass before mutation.
  Receipt: `/private/tmp/floatspec-lpo-contract-controls-v2-20260920.log`.
- Fresh compiled trust: **13,571 declarations / 58 modules / four unchanged
  debts**; freshly exported metadata validates **272** source anchors.
  Receipts use `/private/tmp/floatspec-lpo-{trust,source-metadata,anchors}-20260920`.
- Source and fixture LSP diagnostics complete with zero errors. Demo,
  warning-as-error Python compilation, shell syntax, generated status and
  whitespace checks pass. Status: 99 Lean files, four sorries, no explicit
  axioms/admit. No new proof debt.

The first projection proof split the result match before its existence
condition; the resulting failed `rfl` goals were corrected and retained in
the v1 log. The first Python control emitted an escape-sequence warning;
the warning-free rerun is the reported receipt. Earlier partial LSP results
were not treated as passes; later diagnostics completed. These classical
constructors are not native decision procedures. No universal integer witness
identity across old/new choices or assistants is claimed. The frozen older
broad runner remains active in scaling and integer stages.

### September 20, 17:17 UTC — complete frozen three-loop rerun

The combined `scripts/test_flocq_conformance.sh` process exited **zero** and
emitted its final three-loop success marker. All ten retained bridge reports
have `status: passed`, no mismatches, all requested comparisons and generated
kernel equalities complete, and the same source/configuration fingerprint:
`32ec11b5b0ac7fb6cba5d58635307df2857568f7228c9554e8343d498305dfbf`.
The frozen worktree remains clean and its live hash was checked again after
completion. The run started at `5a6d16df`; later documentation-only commits
through `2e3ea2d1` did not change this source hash. Seed **848933** was used
for the main corpora; replay inputs came from their saved files.

| Stage | Cases / generated kernel equalities | Seconds |
|---|---:|---:|
| Core | 48,614 | 6,122.028 |
| Four saved replays | 197 + 87 + 4 + 4 | Retained per replay |
| Native unary | 622 | 160.299 |
| Native arithmetic | 1,424 | 1,134.211 |
| All-mode IEEE arithmetic | 390 | 551.361 |
| Scale/decomposition | 2,360 | 375.196 |
| Integer rounding/truncation | 1,460 | 247.958 |

Total: **55,162** compared case executions and generated kernel equalities.
All **119** core/native/IEEE bridge-harness tests pass (76 + 10 + 9 + 9 + 7 + 8),
including deliberate mutations, replay, source drift, timeout and interruption
controls. The earlier source-reference and compiled-trust harnesses pass too.
Frozen-snapshot gates validate **228 source anchors** and compiled trust for
**13,537 declarations / 58 modules / four recorded debts**. Pure Lean, pure
pinned Rocq, all fixed fixtures and the seven-part executable demo pass.

Native scope is intentionally bounded. The scale report records 2,032 cases
with fewer native columns (directed modes and exceptional frexp behavior),
and the integer report records 537 such cases. The source compiled/kernel/Rocq
columns are still compared exactly; native exclusions are not agreement
claims. Their explicit checked-column lists remain in each report.

Main log: `/private/tmp/floatspec-full-three-loop-5a6d16df-20260920.log`.
Artifact directories share prefix
`/private/var/folders/gn/1hqqc7pn3nz5s_p0dxnn9h300000gp/T/`:
`floatspec-bridge-1vtmvy__`, replay directories `floatspec-bridge-y_304h67`,
`floatspec-bridge-7e4c1yh5`, `floatspec-bridge-zklr1lvn`,
`floatspec-bridge-9xip4ng4`, `floatspec-native-ieee-7ygru4gb`,
`floatspec-native-arithmetic-gv_j9s4i`, `floatspec-ieee-modes-s8i1men6`,
`floatspec-ieee-scale-h7lmroyh`, and `floatspec-ieee-integer-cxxvjrri`.

This completes the previously pending broad run. It does not cover later
Pff/model-adapter/LPO changes, whose separate receipts are recorded above,
and it does not prove universal source equivalence. The interrupted older run
and earlier timeouts remain errors rather than being overwritten as passes.

### September 20, 17:36 UTC — source ULP witness and preservation boundary

`Core.Ulp.negligible_exp` now projects the repaired `Raux.LPO_Z` result,
following pinned `Core/Ulp.v:45` and the source's nonnegative-then-negated
natural witness construction. The old arbitrary integer `Classical.choose`
was only specification-equivalent; raw witness identity was not established.
The proof of its witness predicate now consumes the carried evidence directly.
The fixed-point zero-ULP proof uses that predicate instead of unfolding the
previous choice implementation. Both proofs remain closed.

A new closed theorem proves that **for every valid radix, valid exponent
function and real input**, the entire new ULP value equals the previous one.
This includes zero. It does not assert identity of arbitrary integer witnesses.
Paired fixtures show the premise matters: the identity exponent function is
invalid and two of its acceptable witnesses, zero and one, give different
binary powers. Exact body guards cover the witness projection, ULP,
positive predecessor, successor and predecessor in both assistants.
Five inspected definition anchors bring the compiler metadata total to 277.

Final source/configuration SHA-256:
`4295264c770099973f8c633b0b0149cd3b7366703a70a85ff732fb1a4fc7a237`.

- Full macOS Lean 4.34 build passes **6,227 jobs**, including the permanent
  fixture; all seven compiled demo examples pass. Receipts:
  `/private/tmp/floatspec-ulp-full-build-v2-20260920.log` and
  `/private/tmp/floatspec-ulp-demo-20260920.log`.
- Source, FIX and fixture LSP checks complete without errors. All eight
  printed fixture axiom lists exclude `sorryAx`; the paired pinned Rocq
  fixture closes without admissions. Receipts:
  `floatspec-ulp-choice-lean-final-20260920.log` and
  `floatspec-ulp-choice-rocq-v2-20260920.log`, under `/private/tmp`.
- All **three live controls** pass (9.799 seconds): both checkers reject
  erasing the zero-spacing branch, and Lean rejects removing the validity
  premise from the preservation proof. Original fixtures compile first.
  Receipt: `/private/tmp/floatspec-ulp-choice-controls-20260920.log`.
- Fresh trust checks **13,568 declarations / 58 modules / four unchanged
  debts**; fresh metadata export then validation checks **277 anchors**.
  Receipts: `/private/tmp/floatspec-ulp-final-{trust,source-metadata,anchors}-20260920`.
  Three fewer generated internal declarations than the previous snapshot
  result from the simpler proof, not removed public exports.
- Generated status: **100 Lean files, four sorries, zero explicit axioms/admit**.
  Shell syntax, warning-as-error Python compilation and whitespace checks pass.

The first proof draft lacked its required radix instance; its failed build
and resulting error-generated sorry were not accepted as a proof. The fixed
fixture has clean final axiom lists. The first Rocq draft needed an `Lra`
import. A later source-validator command used a nonexistent script name;
the fresh export was then validated successfully with the actual validator.
Failed attempts remain in their receipts. No native execution of classical
real ULP, equality of cross-assistant choices, or global source equivalence
is claimed.

The linear reading guide now has a short wake-up summary followed by the
conceptual chapters; detailed chronology stays here. The final seed-859003
Pff/auxiliary/model-adapter stress pass is running against this frozen source
hash. Its outcome will be recorded separately, not assumed.

### September 20, 17:48 UTC — target the Pff neighbor premises

The seed-859003 broad Pff run completed **3,472** cases, all three execution
paths and all generated Lean equalities. It checked **55,012** independent
arithmetic assertions, but its **3,510** conditional neighbor assertions
were unchanged from the older smaller random run. Inspection found why:
the unrestricted bound parameter almost never equals `radix ^ precision`.
This was a coverage gap, not a source/Lean disagreement.

The corpus now adds targeted valid-format samples alongside the unrestricted
ones. A deterministic domain test verifies all premises, signs, zero and
minimum-exponent coverage across 1,000 generated cases. Precision/radix
choices keep the current Nat-transport bound at most 4096. Larger arbitrary
integer mantissas remain in the unrestricted corpus.

A separate **200-case**, seed-**859111** targeted replay passes compiled Lean,
kernel reduction, pinned Rocq and all 200 generated kernel equalities, including
**1,000** premise-gated canonicality/strict-neighbor checks. All **17** Pff
harness tests pass (23.465 seconds). Evidence:
`/private/tmp/floatspec-valid-neighbors-859111/report.json`,
`/private/tmp/floatspec-valid-neighbors-859111.json`, and
`/private/tmp/floatspec-final-pff-targeted-controls-20260920.log`.
Both runs use the unchanged Lean source fingerprint `4295264c…a237`.
The older 3,472-case receipt used the old generator; the new default adds
`samples` additional targeted inputs and must not be assigned its old count.

The preceding final rerun also passed all **41** Pff/aux/model/LPO/ULP/
double-rounding harness tests; the added generator check makes the current
total 42. Fresh direct execution additionally passed 200,200 SingleNaN and
100,100 full-source native arithmetic comparisons, 70,227 Pff exact-rational
helper cases and 60,032 model-adapter inputs / 300,160 observations.
These use their fixtures' retained seeds and the same frozen Lean hash.
Receipts have prefix `/private/tmp/floatspec-final-` and suffix
`-20260920.log`: `pff-controls`, `model-controls`, `lpo-controls`,
`double-controls`, `ulp-controls`, `native-single`, `native-source`,
`pff-aux-oracle`, `model-oracle`, and `pff-walkthrough`.

### September 20, 18:05 UTC — close ULP premise leaks; final snapshot verified

Compiled Rocq types showed twelve ULP laws do not require `Valid_exp`:
`succ_opp`, `pred_opp`, `ulp_opp`, `ulp_abs`, `succ_eq_pos`, `ulp_ge_0`,
`pred_eq_pos`, `ulp_le_id`, `ulp_le_abs`, `ulp_canonical`, `ulp_bpow`
and `pred_bpow`. Two generic-format absolute-value closure laws had the same
extra assumption. The Lean exports and the `pred_eq_pos_flocq` compatibility
wrapper now omit it. The purely integer `fexp_negligible_exp_eq` loses its
unused radix parameter/instance; all repository callers are migrated.
The existing proof bodies remain closed. No arithmetic definition is changed.

Six identical baseline clients failed only with missing `Valid_exp` in Lean
but compiled in pinned Rocq; they now compile in both. The permanent fixture
adds **15 paired typed clients**. All **23** printed Lean fixture axiom lists
exclude `sorryAx`. The shared compiler guard now has **113** source-premise
checks, plus its separate self-tests. The ULP preservation theorem still
requires validity, and its live negative control still rejects removing it.

Final source/configuration SHA-256:
`d53fa1077ac3e66a70bbafd753b9566986a679478866046208fe3ce3901b1f00`.

- Full macOS Lean 4.34 build passes **6,227 jobs**, plus all seven compiled
  demo examples. Logs: `/private/tmp/floatspec-ulp-premise-full-build-20260920.log`
  and `floatspec-ulp-premise-demo-20260920.log`.
- Every added Lean client was checked separately before adding the next.
  Paired Rocq clients, the identical formerly failing Lean clients, and all
  compiled guards pass. Receipts use `floatspec-ulp-premise-clients-final`,
  `floatspec-ulp-premise-clients-rocq`, `floatspec-ulp-symmetry-clients-after`
  and `floatspec-final-premise-guards` under `/private/tmp`.
- All **three** live ULP controls pass again (10.484 seconds). Fresh exported
  metadata validates **277 anchors**; fresh compiled trust checks **13,568
  declarations / 58 modules / four unchanged debts**. Generated status stays
  at 100 Lean files, four sorries, no explicit axioms/admit.
- A final-snapshot replay passes **360 cases and generated kernel equalities**:
  200 targeted Pff cases, 64 seeded auxiliary cases, and 96 model-adapter
  boundary/seeded cases. Each report binds to the final hash above.
  Artifacts: `/private/tmp/floatspec-final-premise-{pff,aux,model}/report.json`.

The immediately preceding stress snapshot `4295264c…a237` separately passed
**8,328** cases: Pff 3,472 (621.806 seconds), auxiliary 3,016 (337.998),
model adapters 1,640 (385.993), and targeted neighbors 200 (58.342).
Their independent assertion counts are 55,012; 15,438; 8,200; and 4,212.
The model run includes 1,161 out-of-range integers and 648 cases where the
source-integer and UInt-model routes differ as expected. These are three-path
finite agreement and policy checks, not native FFI or universal equivalence.

The committed [verification receipt](VERIFICATION_RECEIPT_2026-09-20.json)
keeps the older 55,162-case full run, the newer 8,328-case stress group, and
the final 360-case replay separate, with their complete counts, seeds and
source hashes. Every included report was checked for `status: passed` and
equal requested/comparison/kernel-proof counts before export.

Failed attempts remain explicit. A scratch proof copy omitted its last line;
the complete copied proof passed. The first product patch placed `omit`
after docstrings, which Lean rejects; moving it before the docstrings fixed
the parser errors. Editor diagnostics repeatedly timed out for the large
source modules; those partial responses are not passes. Direct per-client
compilation and the full build supply the source verification. The final
fixture LSP request did complete cleanly. No new sorry was introduced.

### September 20, 18:27 UTC — exact neighbor oracle; hosted CI diagnosed

The new four-hour continuation ends at 22:14 UTC. Live hosted runs
[`35528043323`](https://github.com/alok/FloatSpec/actions/runs/35528043323)
and `35528043110` confirm the known CI setup failure: Lean 4.34.0 is installed,
but the automatic Mathlib cache requires the pinned dependency's 4.34.0-rc2
toolchain. No FloatSpec source compilation occurs in those failed jobs.
The current action also saves its cache before the separate build steps.
The proposed narrow repair retains the dependency pins, disables that
incompatible prebuilt cache, and builds inside the action so it saves completed
artifacts. Approval was requested under the CI workflow; no workflow or
dependency changes have been made in this milestone.

The current CI commands were independently run locally: the full macOS build
passes 6,227 jobs; every listed runtime fixture and the seven-part demo pass;
placeholder/source-linter checks, compiled trust (13,568 / 58 / four debts),
the listed Python tests, and generated-status consistency pass. The CI-style
Python run deliberately had no `FLOCQ_AUDIT_DIR`, so its live Rocq tests were
**skipped**, exactly as on the current hosted configuration. This is not
three-loop CI coverage. `actionlint` v1.7.12 finds no workflow syntax errors;
the failure is the cache policy, not YAML parsing.

The Pff independent oracle now checks exact adjacency as well as canonicality
and strict order. It searches bounded integer grids using exact rational
floor/ceiling, stopping once the positive grid unit exceeds the input's absolute
value. It does not duplicate Flocq's normalization/neighbor branches. An
independent finite enumeration checks 180 queries across four radices, three
precisions, and three minimum exponents.

Two new controls mutate **all three** observation streams to the same canonical
but nonadjacent answers: at base three/precision two, successor of one `5/3`
instead of `4/3`, and predecessor `7/9` instead of `8/9`. Both are rejected.
All **19** Pff harness tests pass with live pinned Rocq (21.073 seconds);
the 15 non-live profile checks pass again after adding report metadata.
The retained seed-859111 replay passes **200 cases / 200 kernel equalities**,
with **4,612** independent assertions, including **1,400** premise-gated checks
and **400** exact adjacency assertions (35.921 seconds). Reports and logs:

- `/private/tmp/floatspec-adjacency-final-859111/report.json`
- `/private/tmp/floatspec-pff-adjacency-controls-20260920.log`
- `/private/tmp/floatspec-pff-adjacency-profile-controls-20260920.log`
- `/private/tmp/floatspec-ci-local-build-20260920.log`

The Lean/configuration hash remains `d53fa107…b1f00`; no product definition,
theorem, or proof debt changes. The earlier first adjacency replay also passed
but recorded the unused default CLI seed `20260919`; its inputs were the same
saved seed-859111 corpus. The final replay explicitly supplies that seed and
includes the oracle description. Historical reports retain their original
weaker assertion counts. Finite tests are not a universal adjacency proof.

### September 20, 18:36 UTC — seven unrestricted neighbor laws

Pinned Rocq's compiled types for `pred_pos_lt_id`, `succ_gt_id`, `pred_lt_id`,
`succ_ge_id`, `pred_le_id`, `succ_0`, and `pred_0` contain no `Valid_exp` premise.
The former Lean types all contained it. A matching unrestricted predecessor
client compiled in Rocq but failed in Lean solely at instance synthesis.
All seven public exports and five private supporting lemmas now omit the
accidental section instance. Their proof bodies are unchanged; no new sorry
is used. Seven pinned anchors, paired typed clients, and compiler guards
were added. The public legacy Hoare wrappers remain compatible.

Verification on source/configuration hash
`5d2419162276975de050051816be91dc8af1562adeeeb4fc28bb07eea3974cfe`:

- The identical previously failing Lean client now compiles; all seven new
  fixture proofs were checked separately before adding the next.
- All seven paired Rocq clients pass; all 30 printed fixture axiom lists
  exclude `sorryAx`. The three live zero-spacing/validity mutation controls
  pass (10.448 seconds).
- Full macOS Lean 4.34 build passes **6,227 jobs**, and the compiled seven-part
  demo passes. The shared gate now has **120** source-premise checks and
  nine separate self-test commands (seven negative, two positive).
- Fresh compiled trust remains **13,568 declarations / 58 modules / four
  recorded debts**. Freshly exported metadata validates **284** pinned anchors.
  Status remains 100 Lean files / four sorries / no explicit axioms or admit.
- LSP fully checks the changed source module and, after rebuilding imports,
  both test files without errors. Earlier per-client partial/time-out LSP
  responses are not passes; direct compiler checks supplied those results.
  One initial helper annotation followed its docstring and caused a parser
  error; placing `omit` before the docstring fixed it before the source build.

Logs use `/private/tmp/floatspec-neighbor-premise-` followed by
`slice`, `full-build`, `controls`, `trust`, or `demo`, then `-20260920.log`;
the metadata and trust JSON files use the same prefix/date.
The baseline probe files are `/private/tmp/UlpNeighborPremises20260920.lean`
and `.v`, and the post-fix client output is
`/private/tmp/floatspec-neighbor-client-after-20260920.log`.
No arithmetic definition body changed. Finite replay of earlier snapshots
must not be relabeled as execution of this new fingerprint.

### September 20, 18:40 UTC — concurrent comparison commits are not source-equivalent

Read-only review of the original checkout found three unmerged Claude commits
(`ff02ad28`, `f5d01e1d`, `8b81a532`) based on older ancestor `f95c7407`.
Their new dyadic comparison backend is proved equal to the old real-valued
Lean specification, but that is not the raw Rocq comparison contract.
The exact copied backend returns equality on positive `(3,-1)` versus `(6,-2)`;
both the current source-facing Lean API and actual Rocq `SpecFloat.SFcompare`
return greater-than. All three results were executed and the concrete
inequality was kernel-checked in Lean. The paired source regression already
retains this case. These commits were not merged, and the original worktree
and modified dependency were not edited.

The [focused review](CLAUDE_COMPARISON_REVIEW_2026-09-20.md) records the inspected
definitions, exact probe scope, counterexample, documentation corrections,
and possible distinct use for the arbitrary-dyadic-value helpers. It does not
claim the internal dyadic-value equivalence proofs are invalid. The mistake
is identifying their old Lean target with the actual raw source API.
The fresh full three-loop run remains in progress on `5d241916…974cfe`;
this review changes documentation only and does not disturb that snapshot.

### September 20, 19:04 UTC — independent exact IEEE expectations

Added a separately runnable finite-input IEEE oracle based on exact rational
grid selection, not a translation of the source rounding algorithm. Square
root compares squared integer midpoints rather than approximating a root.
The oracle handles all five rounding modes, both IEEE widths, gradual
underflow, finite overflow, signed zero, and fused single-rounding semantics.
NaN/infinite-input arithmetic, zero divisors and negative roots are explicitly
excluded; no result is invented for those cases.

All **14 tests** pass with the pinned reference enabled (30.742 seconds):
twelve unit/receipt controls and two actual live Lean/Rocq tests. Controls
compare selection with enumerated six-bit representable grids, check known
IEEE boundaries, reject common wrong-rounding/input mutations across every
path, and reject incomplete saved reports. The live tests freshly execute
**40 all-mode cases and seven native pairs**, check **6,738 expected fields**,
and generate **47 Lean kernel regression proofs**.

A separate retained initial live run also passed those 47 cases (30.257 seconds),
with report `/private/var/folders/gn/1hqqc7pn3nz5s_p0dxnn9h300000gp/T/floatspec-exact-oracle-live-51edbt8o/report.json`.
It is bound to current Lean/configuration fingerprint `5d241916…974cfe`.
The reproducible live test log is
`/private/tmp/floatspec-exact-oracle-tests-20260920.log`.

The saved-report checker separately audits earlier source snapshot
`32ec11b5…5dfbf`: 1,424 native arithmetic cases pass **31,072** independent
field assertions, and 390 all-mode cases pass **45,090**. These are new checks
of retained old observations, not fresh execution of today's source. The
original report paths remain in the machine-readable historical receipt.

No running bridge script or Lean source was changed, so the large seed-859733
aggregate keeps its frozen source and harness. The new oracle and receipt
checker are standalone pending integration after that run. CI's narrow
cache-policy repair still awaits approval. No proof debt was added.

### September 20, 19:08 UTC — a concrete boundary for assumption removal

The new paired `ExponentValidityBoundary` fixtures prove six declarations in
each assistant. The same alternating exponent function is valid, not monotone,
and represents every power of two; nevertheless its ULP decreases from `1/2`
at input `1/2` to `1/4` at input one. This demonstrates why pinned `ulp_le_pos`
and `ulp_le` genuinely require `Monotone_exp`, which the current Lean types keep.
It is a counterexample to dropping that premise, not a source-conformance bug.

Each new Lean proof was checked before the next was added. Final LSP diagnostics
complete without errors; direct Lean compilation and pinned Rocq compilation
both pass. Six printed Lean axiom lists exclude `sorryAx`; the paired Rocq
lists expose their ordinary classical-real assumptions. Logs:
`/private/tmp/floatspec-exponent-boundary-lean-20260920.log` and
`/private/tmp/floatspec-exponent-boundary-rocq-final-20260920.log`.
An initial Rocq output path had a basename different from its source and was
rejected before compilation; using the matching basename passed. Earlier
scratch errors from an ambiguous Lean alias and proof syntax were corrected
before the final fixture was added.

The standalone fixture and linear explanatory table do not change any imported
Lean source, existing harness or dependency. The running source fingerprint
remains `5d241916…974cfe`. The current Generic_fmt validity docstring loosely
calls the large-regime condition monotonicity; its formula is correct, and
that wording should be corrected after the source-frozen run.

### September 20, 19:38 UTC — 27 further Core contracts restored

Compiled types were surveyed for 266 same-named exports in Generic_fmt,
Ulp, Round_NE and Float_prop (270 requests included four duplicate names).
Manual inspection of the selected differences confirmed 27 extra
`Valid_exp` premises: sixteen in Generic_fmt and eleven in Ulp. The full
list is pinned by `scripts/fixtures/CorePremiseBoundary.lean` / `.v`;
every expected client type compiles in its own assistant. This survey is
not a full semantic review of all 266 exports.

All 27 premises and the necessary supporting helper premises are removed.
Three rounding proofs now exploit exact binade magnitude instead of a
weaker bound plus exponent validity. The floor/ceiling ULP-gap proof
directly reconstructs a generic value if the scaled mantissa is integral.
Other proof bodies and all arithmetic definitions are unchanged.
The genuine monotonicity premise on `succ_le_plus_ulp` remains. The
Valid_exp docstring now states the actual transition/constancy conditions,
not the incorrect shorthand “monotonicity.”

Each changed mathematical proof was checked individually before proceeding.
The full macOS Lean 4.34 build passes **6,226 jobs**; all seven demo examples
pass. Complete final LSP diagnostics report no errors for the changed
proofs and 27 clients. Every client axiom list excludes `sorryAx`.
The direct source-premise run passes **147 guards**, including the 27 new
ones. Fresh metadata validates **311 anchors**. The compiled trust audit
still reports **13,568 declarations / 58 modules / four exact manifest
debts**, with no new direct or propagated debt.

The independent IEEE suite was rerun on this source: **14 tests pass**
in 30.847 seconds, including 47 live cases, 47 generated kernel equalities
and 6,738 independent expected-field checks. This is a fresh small
execution, not completion of the separately running large aggregate.
The new source fingerprint is
`eb306bb511c7c42deea5750a87753ca53b8168e51ea701c4acde55319e722eb6`.
Development uses a new isolated `codex/astra-premise-boundary` worktree;
the `5d241916…974cfe` aggregate remains frozen in its earlier checkout.

Receipts: `/private/tmp/floatspec-core-premise-full-build-20260920.log`,
`floatspec-core-premise-client-27-20260920.log`,
`floatspec-core-premise-clients-rocq-20260920.log`,
`floatspec-core-premise-trust-20260920.json`,
`floatspec-core-premise-anchors-20260920.log`, and
`floatspec-core-premise-exact-oracle-20260920.log`, all in the same
`/private/tmp` directory. Early helper-dependency and rewrite failures
were corrected before the final successful builds; they are not passes.
Hosted CI's cache-policy change remains approval-pending.

### September 20, 19:50 UTC — independent expectations become bridge gates

The native-arithmetic and all-rounding-mode runners now check every observed
path against the independent exact IEEE oracle. Reports keep
`oracle_assertions`, `oracle_mismatches` and a precise finite-input scope,
separately from pairwise mismatches. Either failure class rejects the run and
retains deduplicated replay inputs. Kernel bootstrapping is withheld when the
logical observation itself fails the oracle; an isolated native/compiled
failure can still retain a sound logical regression.

All **20 integrated harness tests pass** with the live pinned Rocq source:
10 native tests in 36.538 seconds, 10 mode tests in 39.660 seconds.
Two new deliberate shared bugs execute actual programs: swapping operands
before every native/model/Rocq path, and replacing upward rounding with
nearest-even in every Lean/Rocq mode expression. Pairwise mismatches are empty
in both controls, but the new independent gate rejects them, preserves the
inputs, and generates no misleading kernel regression. Existing single-path
mutation, interrupted-process and timeout controls still pass.

The standalone oracle unit refresh passes twelve controls (two live tests
explicitly skipped); the preceding same-source live refresh already passed
all fourteen. The full macOS build and shell syntax check pass. The aggregate
runner now includes the oracle suite and both new paired Core/exponent
fixtures. Its previous frozen copy is intentionally unchanged, so this is
not a claim that the older aggregate ran these newly integrated commands.
Fresh seed-861047 native and all-mode executions are now running on
`eb306bb5…722eb6`; neither is yet counted as complete.

Logs: `/private/tmp/floatspec-integrated-native-oracle-tests-20260920.log`,
`floatspec-integrated-modes-oracle-tests-20260920.log`,
`floatspec-integrated-oracle-unit-20260920.log` and
`floatspec-integrated-oracle-build-20260920.log`.
No Lean definition, theorem or proof debt changes in this integration.

### September 20, 20:18 UTC — eight nearest-policy contracts restored

Eight ULP exports accepted a nearest tie policy while their statements used
the fixed `round_N_to_format` chooser: `round_N_eq_DN`, `round_N_eq_DN_pt`,
`round_N_eq_UP`, `round_N_eq_UP_pt`, `round_N_eq_ties`, `round_N_plus_ulp_ge`,
`round_N_le_midp` and `round_N_ge_midp`. In particular the old two-policy
agreement proposition was a reflexive fixed-value equality. This is a source
contract defect, not a counterexample to the old tautological proposition.

All eight public source statements now preserve the supplied choices through
`roundR`/`round_to_generic` and `Znearest`, with direct propositions and pinned
source links. Six have new short closed proofs; the lower-midpoint bound is
proved by negation, and the upper-midpoint bound reuses its previously private
choice-preserving proof. Old payload compatibility exports receive explicit
names; four now-unused private fixed-policy helpers are removed. The old
chooser's body and type are unchanged, and its metadata/docstring explicitly
describe a Lean-local ties-up policy. No arithmetic definition is changed.

The final macOS Lean 4.34 build passes **6,226 jobs**, as do all seven demo
examples and all **147 source-premise guards**. Fresh compiler metadata
validates **319 pinned anchors**; compiled trust covers **13,565 declarations
/ 58 modules / four exact manifest debts**, with no new debt. The paired
fixtures compile eight typed clients, prove the `1/2 → 0` versus `1/2 → 1`
choice distinction, and actually evaluate the integer decision `[0, 1]` in
both assistants. All ten Lean axiom lists exclude `sorryAx`; the executable
example is axiom-free. Complete final client LSP diagnostics contain no errors.
All **four live mutation tests pass** in 32.011 seconds, rejecting erased
second-choice types and incorrect midpoint answers in both assistants.

This source has fingerprint
`687aa7a88bdb9b5d4d3a7ac34b39b2b16efe7f265514e28b03039e76257395d2`
in `codex/astra-ulp-nearest-boundary`. The separately frozen `eb306bb5` runs
also finished: native arithmetic **1,104 cases / 1,104 kernel equalities /
22,672 independent assertions**, and all modes **390 cases / 390 kernel
equalities / 44,955 independent assertions**. Both exit zero with empty
pairwise and oracle mismatches; seed **861047**. Reports preserve launch HEADs
and dirty-path records rather than being retroactively relabeled. These
1,494 executions are not a runtime receipt for the later eight theorem changes.
The earlier `5d241916` aggregate is still running, not yet a pass.

Final receipts: `/private/tmp/floatspec-eight-choice-full-build-20260920.log`,
`floatspec-eight-choice-client-final-20260920.log`,
`floatspec-eight-choice-trust-20260920.json`,
`floatspec-eight-choice-anchors-20260920.log`,
`floatspec-eight-choice-premises-final-20260920.log`,
`floatspec-choice-mutation-tests-final-20260920.log`, and the
`floatspec-integrated-{native,modes}-oracle-861047/report.json` directories.
Initial namespace/rewrite errors were corrected and rechecked. One direct
client run overlapped a build and failed on a temporarily missing import;
the final run after build completion passed. An incorrectly named guard-file
command failed and was rerun with the actual `SourcePremiseContracts.lean`.
None of those failed attempts is counted as a pass. CI repair remains pending
approval; the original checkout and modified Flocq dependency remain untouched.

### September 20, 20:30 UTC — exceptional inputs enter the independent IEEE gate

The exact rational/grid oracle now includes a separate exceptional-value
classifier: infinities, zero divisors, negative square roots, and NaNs with
pinned Flocq's first-input-payload policy. The native observation route
canonicalizes NaNs in both inputs and results; full-payload source routes do
not. FMA distinguishes an exact finite product from a prematurely overflowing
rounded product. Hardware exception flags are not modeled.

All **16 oracle tests pass** in 34.552 seconds: fourteen unit/receipt controls
and two live tests with **47 fresh cases, 47 kernel equalities and 7,036
independent expected-field checks**. All **22 bridge-harness tests pass**:
twelve all-mode tests in 54.552 seconds and ten native tests in 37.697 seconds.
Two new controls first execute an unmodified baseline, then mutate every actual
Lean/Rocq expression to agree on a wrong exceptional answer: treating infinity
times zero in FMA as zero, and reversing first-NaN payload priority in addition.
The independent gate rejects both, retains replay inputs and generates no
misleading kernel regressions. Baseline pairwise agreement is not treated as
sufficient evidence.

The saved seed-861047 reports also pass the expanded expectations: **30,912
native fields plus 66,690 all-mode fields = 97,602 assertions**. Those are
new audits of the preceding eb306bb5 execution, not fresh executions or
687aa7a8 runtime claims. The fresh 470-case mode run on 687aa7a8, seed
862073, subsequently passed in 735.288 seconds: 470 kernel equalities and
80,370 independent assertions, no mismatches. The fresh 1,104-case native
run, seed 862081, is still underway and is not yet a pass.
The older 5d241916 full aggregate remains running and frozen.

Logs: `/private/tmp/floatspec-exception-oracle-live-20260920.log`,
`floatspec-exception-{modes,native}-harness-20260920.log` and
`floatspec-exception-{native,modes}-retained-audit-861047.json`.
No Lean definition, theorem, toolchain or proof debt changes in this slice.
The final preceding full build remains applicable to the identical Lean
source fingerprint. The reading guide now links an explicit fidelity gap list,
distinguishing known interface gaps, unreviewed semantics, provenance coverage,
test scope and native proof obligations.

### September 20, 20:47 UTC — integrate the continuation in the normal checkout

At the user's direction, development is now in `/Users/alokbeniwal/FloatSpec`
on `main`; `~/floatspec` denotes that same directory on this filesystem.
`origin` is the user's fork, `main` tracks `origin/main`, and BAIF remains the
optional `upstream`. The old local main was an ancestor and fast-forwarded.
Claude's three comparison commits are retained in history and their useful
implementation is integrated with explicit semantic boundaries.

The executable exponent-alignment bodies and dyadic-value proofs are preserved.
The four old real-valued comparison definitions are exposed as local
`ComputableCompare.ValueSpec` specifications. Twelve correspondence theorems
are renamed `*_eq_value` and target that specification, not Flocq's raw API.
All twenty public definitions are locally classified and the source linter
is enabled for this module. No existing noncomputable marker was removed;
the user's question about it was answered using unchanged-source Lean/Rocq
probes. The corrected linear implementation guide records the distinction.

Both modified Lean files have complete clean LSP diagnostics. Earlier partial
or unavailable responses were not counted as passes; incremental compiler
checks first exposed the old raw-equivalence claims, then all adapted proofs
checked without new sorries. The 20,000-pair executable test passes. Additional
kernel regressions distinguish equal values from unequal raw comparisons.
The full macOS Lean 4.34 build passes **6,226 jobs**, the seven-example demo
passes, and the paired 24-case raw-comparison fixtures pass in Lean and Rocq.
Fresh trust audit: **13,667 declarations, 59 modules, exactly four recorded
direct/transitive proof debts**. Fresh metadata validates **319 source anchors**.
Integrated Lean source hash:
`4b714ddb87364ecf504600c50bc1421d89b61b91080f5926d742f2e1d5d30795`.

A fresh raw-comparison bridge on this integrated source passes **1,237 cases**
and 1,237 generated kernel equalities, seed 862149, in 156.894 seconds.
Its report is `/private/tmp/floatspec-main-comparison-862149/report.json`.
The first command used the nonexistent family spelling `primitive_comparison`
and exited with an argument error before execution; the corrected family is
`prim_comparison`. That rejected invocation is not a test pass.

The preceding frozen `687aa7a8` native run also finished: seed 862081,
**1,104 cases/kernel equalities and 30,912 independent assertions**, no
mismatches, 1,074.270 seconds. Combined with the 470-case all-mode run,
that gives **1,574 cases and 111,282 independent assertions** on that snapshot.
These are not relabeled as executions of the additive main integration.

Logs: `/private/tmp/floatspec-main-merged-{full-build,trust,anchors,demo}-20260920.log`,
`floatspec-main-compare-execution-20260920.log`, and the seed-862081 report.
The original dependency is still at `54cadd27` with the same seven untracked
analysis files. The gitlink stays pinned at `7aab8f55`; no dependency checkout,
reset or submodule update was performed.

### September 20, 21:12 UTC — unindexed Pff zero and multiplication

The source facade now exports `Fzero`, `is_Fzero`, `Fmult` and four fully
proved observer laws, each linked to the pinned Pff source. Actual Rocq
export types confirm the hypothesis boundary: the two forward zero laws
need no radix restriction, zero's converse retains `1 < radix`, and the
multiplication law requires only `0 < radix`, including radix one.
The facade does not silently impose the indexed Core carrier's stronger
radix restriction. No existing `noncomputable` marker was changed.

Paired typed clients exercise all seven exports, preserve the requested
exponent in a zero record, accept multiplication at radix one, and prove
that dropping positivity entirely admits a radix-zero counterexample.
The four observer proofs and Lean counterexample have no `sorryAx`;
the two executable record constructors have no axioms. Both complete
LSP diagnostics and the final paired Lean/Rocq compiles pass. Initial
fixture failures (ambiguous source names, missing Rocq `Lia`, and a
redundant rewrite after simplification) remain failures, not test passes.

The differential profile grows from 56 to 61 observations. It compares
actual pinned Rocq, Lean kernel reduction and compiled Lean results, then
checks exact record/value expectations independently. All **20 harness
tests pass with live Rocq enabled** in 45.576 seconds. The tests mutate all
61 output columns and deliberately change both provers' actual programs
to agree on the same wrong zero exponent or multiplication sign. The
independent gate rejects those shared errors, retains replay inputs and
does not bootstrap misleading kernel regressions.

Fresh seed **862307** passes **3,072 cases**, **3,072 generated kernel
equalities**, **65,846 independent assertions**, including **7,014
conditional neighbor assertions**, in 665.199 seconds. This is finite
evidence across invalid radices/bounds and large integer inputs, not
universal source equivalence. Source fingerprint:
`21a75295de260d1079eec62944ca54dadc80a541b760d9926ef37ec97fced48d`.
Report: `/private/tmp/floatspec-main-pff-basic-862307/report.json`.

The full macOS Lean 4.34 build passes **6,226 jobs**; fresh compiled trust
checks **13,678 source declarations / 59 modules**, with exactly the same
four manifest-only direct/transitive debts. Fresh metadata validates
**326 source anchors**. Logs are
`/private/tmp/floatspec-main-pff-basic-{full-build,trust,anchors,live-final}-20260920.log`.
The reading guide's opening is condensed into a current summary and
snapshot-specific evidence table. The broad frozen `5d241916` aggregate
is still running, and hosted CI still awaits the proposed cache repair.

### September 20, 21:21 UTC — direct nearest-even point contract

`RoundNE.round_NE_pt` now returns the concrete nearest-even correctness
proposition directly. The prior closed Boolean/Hoare proof is retained as
`round_NE_pt_check_spec`, and both production Pff callers now use the direct
result. Pinned anchors cover the positive and all-input point exports.
No numerical body, predicate, source premise or existing noncomputable marker
changed; no new proof debt was introduced.

Paired `RoundNEPointContracts` clients freeze the four compiled export types:
negation without exponent assumptions, absolute value with `Valid_exp`, and
the two point theorems with `Valid_exp` and `Exists_NE`. All four Lean axiom
lists exclude `sorryAx`. Four mutation controls first compile their baselines,
then reject an existence-only result or removal of the actual `Exists_NE`
premise in both assistants; all pass in 16.082 seconds.

The first incremental caller build correctly rejected the second, not-yet-
migrated caller. After migrating that caller, the full macOS Lean 4.34 build
passes **6,226 jobs**. Core and fixture LSP diagnostics are complete and clean;
Pff auxiliary LSP diagnostics remained unavailable after dependency rebuilding,
so its successful compiler/full-build checks are the evidence instead.
Fresh compiled trust checks **13,680 source declarations / 59 modules**, with
the same four recorded direct/transitive debts; **328 source anchors** validate.
Source fingerprint:
`b9b5abb6161724b5647c56beb8bae05cc8960dbc2137da7273e4eabc58bc50f6`.
Logs: `/private/tmp/floatspec-main-round-ne-{full-build,trust,anchors,mutations}-20260920.log`.
The previous Pff execution remains bound to `21a75295`; theorem/API changes
are not relabeled as a fresh run of the arithmetic bridge.

### September 20, 21:50 UTC — remainder premises and completed full aggregate

The four remainder exports `format_REM_aux`, `format_REM`, `format_REM_ZR`
and `format_REM_N` match the pinned source contracts at lines 638, 772, 837
and 858. Their production bodies, types and proofs are unchanged; four
source anchors are added. Paired typed clients retain exponent validity,
monotonicity and the actual small-quotient condition. The general and
specialized theorems do not acquire a spurious nonzero-denominator premise.

Both assistants prove that upward quotient rounding does not preserve
representability in general: with two-bit precision, `1` and `8` are
representable, but `1 - ceil(1/8)*8 = -7` is not. The Lean proofs and the four
imported contracts have no `sorryAx`. A separate finite grid proves and
executes all 12,100 combinations of 55 signed inputs and four integer
quotient test modes: 11,582 meet the premise, 518 do not, and 380 outside
the premise actually have inexact remainders. There are 220 mathematical
zero-divisor cases. No claim is made that these test quotient models are
universal executable refinements of the real-valued definitions.

The new three-way bridge executes actual source `binary_round`, compares
six observations, independently enumerates an exact rational representable
grid, and bootstraps kernel Lean equalities. Seed **862513** passes
**12,100 cases**, **12,100 generated equalities**, and **84,182 independent
assertions**, without mismatches, in **453.569 seconds**. It saves both the
Lean source hash and paired protocol hash. Six contract mutation controls
pass in 122.313 seconds; six bridge tests pass in 15.984 seconds, including
shared actual-program mutations from truncation to floor and from rounding
to an unrounded raw constructor. The independent oracle rejects the shared
wrong outputs and prevents generating misleading regressions.

Initial fixture elaboration errors and two overly narrow expected-error
matchers remain recorded failures. In particular, a false kernel assertion
can be followed by a runtime success message: the nonzero compiler exit is
still an error, never a pass. Accepted fixture LSP diagnostics are complete
and clean. Production-file LSP remained incomplete; the full compiler build
is its verification evidence. The full macOS Lean 4.34 build passes
**6,226 jobs**; trust checks **13,680 source declarations / 59 modules** and
the same four manifest-only direct/transitive debts. **332 anchors** validate.
Source hash: `3c5a913de4d373b323c56b8f5b805417766a6644a5e175ea0308e17488fce127`.
Report: `/private/tmp/floatspec-remainder-862513/report.json`.
Logs: `/private/tmp/floatspec-remainder-{full-build,trust,anchors}-20260920.log`,
`floatspec-remainder-mutations-accepted-20260920.log` and
`floatspec-remainder-bridge-harness-20260920.log`.

The separately frozen **5d241916** aggregate also completed with exit zero
at 21:43 UTC. Its thirteen differential reports total **60,639 executions
and generated kernel equalities**, including replays; **168 harness tests**
pass. Those reports cover core, native unary/arithmetic, all modes,
scale/decomposition, integer rounding, Pff, Pff auxiliary and model adapters.
They do not run current main and their older IEEE profiles do not include
the later independent exceptional oracle. All report paths, seeds, exact
hashes and per-profile timings are in the verification receipt. Aggregate
log: `/private/tmp/floatspec-four-hour-full-three-loop-859733-20260920.log`.
Do not sum overlapping snapshot groups into unique-input coverage.

The generated status report is refreshed to 102 Lean files and now explains
that its textual placeholder heuristics are not a semantic source audit.
No existing `noncomputable` marker was changed in this slice.

### September 20, 22:00 UTC — why monotone exponents matter for remainders

The paired `ExponentValidityBoundary` fixture now checks eleven declarations.
Its valid but nonmonotone exponent function admits `7/4` and `1`, but excludes
`3/4`. Both assistants prove that truncation remainder preservation therefore
fails without exponent monotonicity. This is a genuine source premise, distinct
from the small-quotient premise tested in the preceding slice. All eleven Lean
axiom lists contain only standard axioms; no admitted proof was introduced.
Complete fixture LSP diagnostics and direct Lean/Rocq compilation pass.

The ULP theorem also addresses the user's diff comment: its conclusion now
directly negates monotonicity on nonnegative inputs. The facts `0 ≤ 1/2 ≤ 1`
are used internally to instantiate the overbroad claim, not conjoined with the
interesting result. The matching Rocq statement has the same shape.

The expanded remainder contract suite passes all **eight live controls** in
**117.019 seconds**, including rejection of deleting `Monotone_exp` in either
assistant. The full macOS Lean 4.34 build again passes **6,226 jobs**. This
slice changes standalone fixtures, tests and explanations only; the production
source fingerprint remains `3c5a913d` and the existing bridge receipt remains
bound to that snapshot. Logs: `/private/tmp/floatspec-exponent-remainder-lean-20260920.log`,
`floatspec-exponent-remainder-rocq-final-20260920.log`,
`floatspec-remainder-monotone-controls-20260920.log`, and
`floatspec-final-2214-full-build-20260920.log`.

Two initial Rocq invocations failed before checking the fixture: the first
used a different output basename, and the second resolved Rocq 9.1 on PATH
against the pinned checkout's 9.2 artifacts. Explicit `/opt/homebrew/bin/coqc`
with a matching basename succeeds. These rejected invocations are not passes.
The latest hosted main run, **35539977225** at `4f8e439f`, again fails at the
Mathlib cache step (final Lean 4.34 versus pinned Mathlib rc2), before project
source compilation. CI policy remains unmodified pending approval.

### September 20, 22:08 UTC — four unindexed Pff sign laws and final checks

The facade now exports `Fopp_correct`, `Fopp_Fopp`, `Fabs_correct` and
`Fabs_Fzero`, with four pinned anchors and closed proofs. The existing numerical
bodies are unchanged. Compiled Rocq client types confirm unrestricted-radix
negation, radix-free involution and nonzero preservation, and positive-radix
absolute-value interpretation (including radix one). Both assistants prove
the latter cannot extend to all negative radices. The extended paired basic
fixture checks all four types and axioms. Four live mutation controls pass in
14.440 seconds, rejecting identity negation and deleting radix positivity.
The source-shaped addition/subtraction observer laws remain a known facade
gap; their source types require only positive radix, not the stronger Core
valid-radix assumption. They are recorded as remaining work, not silently
counted as covered by indexed theorems.

The full macOS Lean 4.34 build passes **6,226 jobs**. Fresh trust checks
**13,687 source declarations / 59 modules**, still exactly four manifest-only
direct/transitive debts; **336 source anchors** validate. Complete production
and fixture LSP diagnostics pass. Final production source fingerprint:
`d0ab66b2bc31ba456e8e344f75cf4fbfafa4b29d89857bc153511599c1e429da`.
A new persistent 72-input sign/radix replay passes all three execution paths,
all generated kernel equalities and **1,272 independent assertions**, seed
862619, in **17.638 seconds**. It deliberately has no conditional neighbor
coverage and is not a replacement for the preceding broader Pff run.
Report: `/private/tmp/floatspec-final-pff-sign-862619/report.json`.
Logs: `/private/tmp/floatspec-final-pff-sign-{full-build,trust,anchors,bridge}-20260920.log`,
`floatspec-pff-sign-contracts-{lean,rocq}-20260920.log`, and
`floatspec-pff-sign-contract-mutations-20260920.log`.

Immediately before these four theorem-only additions, the final standalone
sweep on **3c5a913d** re-executed **14 Lean test modules, 26 standalone Lean
fixtures, 38 pinned Rocq fixtures, and all seven demo examples**. Every command
completed successfully; cached Lake artifacts did not skip the runtime loops.
This includes integer/bit/order/native arithmetic checks, source premise
guards, error-law grids and the new 12,100-case remainder grid. The old aggregate,
this standalone sweep, and the final focused replay are separately fingerprinted
in the receipt, not described as one universal test of final main.

Verification-tool regressions also pass: two compiled-trust tests, three
source-anchor tests, the protected/public-axiom/runtime-override textual
controls, and strict source-linter controls for mutual/private/qualified
definitions and abbreviations. The generated status matches a fresh scan.
No existing noncomputable annotation was changed during the user's explanatory
question or these final slices. No new proof debt was introduced.

### September 21 — stable 4.34 CI repair and exact Pff arithmetic observers

The user approved the stable Lean 4.34 CI repair. Commit `40a336d7` disables
the incompatible rc2 Mathlib binary cache without changing reviewed source
pins, and builds inside lean-action so completed artifacts can be cached.
Actionlint, YAML assertions and the local 6226-job build pass. Hosted run
`35548504304` is still in progress; no hosted success is claimed yet.

The facade now supplies `Fplus_correct` and `Fminus_correct`, both with closed
proofs and the pinned source's `0 < radix` premise. These are genuinely
unindexed clients, including radix one, not renamed Core indexed theorems.
Paired Lean/Rocq fixtures check exact types and prove that radix zero invalidates
the observer laws when exponent alignment crosses zero. Eight live contract
mutations pass (29.359 seconds), rejecting missing positivity and incorrect signs.
Numerical bodies are unchanged. Full macOS build passes 6226 jobs; LSP reports
no errors for production and fixture. The source fingerprint is
`1fb9f1359ff3faa895fa68e8340a58a31c63eb194db6cdfcd2e61c04b1160510`.
Fresh seed 863101 executes the persistent 72-input Pff replay in all three
paths and proves all generated kernel equalities, with 1272 independent
assertions in 17.550 seconds. It has no conditional neighbor coverage.
Report: `/private/tmp/floatspec-pff-addition-863101/report.json`.
No new sorry or axiom was added; the four manifest debts remain unchanged.

### September 21 — executable Pff integers and constructive bounded divisibility

Four previously unnecessary `noncomputable` annotations are removed from
`Pdiv`, `oZ`, `oZ1` and `Zquotient`; their bodies and types are unchanged.
`maxDiv` now selects its decision with the existing `ZdividesP`, as the source
does, instead of `Classical.propDecidable`. A closed Lean fixture theorem proves
equality with the old classical definition for all integer radices/values and
natural bounds. No new proof debt is used. Six pinned links identify these
executable exports, including the existing divisibility checker.

Paired standalone fixtures cover signed and zero-divisor quotients, full
optional-positive records, smallest positives, divisibility argument order,
and negative/zero/one-radix bounded divisibility. The Lean native fixture also
checks 4096 positive divisions. The independent bridge oracle uses rational
truncation, natural division, and finite enumeration of divisible powers.
Seed **863307** passes **2172** compiled/reduced/Rocq cases and generated kernel
equalities, with **6198** independent assertions including twelve zero-divisor
quotient cases, in **160.604 seconds**. Source fingerprint:
`b2e86f6337767c162831fba5e81932fe970324448d9d10b02967e020d54ad975`.
Report: `/private/tmp/floatspec-pff-integer-863307/report.json`.

Eight harness tests pass in 53.406 seconds. Five live mutations corrupt both
actual prover programs together (floor division, swapped quotient/remainder,
false option tag, reversed divisibility, zero search bound); the independent
gate rejects each before bootstrap and retains its replay. Error/interrupt
controls and batching guards also pass. These tests are integrated into the
three-loop script; hosted CI runs the independent Lean fixture and non-live
harness tests, not an invented Rocq installation.

Development failures are not passes: the first fixture needed explicit Nat-to-Int
casts; a mock test initially lacked a compiler override; random zero denominators
required counting fixed boundaries separately. The first corpus interleaved
capped families and was explicitly interrupted after 278 checked cases; its
report remains `error` with `KeyboardInterrupt`. Grouping inputs fixes the
excessive per-case prover startups without dropping cases. The first maxDiv
mutation triggered an unused-variable warning rejected by the strict parser;
the corrected executable mutation uses `bound - bound` and is rejected for
its wrong numerical result. The successful receipts above are fresh reruns.

Final local gates pass: the full macOS Lean 4.34 build completes 6226 jobs;
compiled trust checks 13692 source declarations across 59 modules with exactly
the four existing manifest-only debts; fresh metadata validates 344 pinned
anchors. Generated status is unchanged and whitespace/actionlint/shell syntax
checks pass. Production Pff LSP queries remain partial on this large file;
the completed compiler build, not those partial responses, is the decisive
whole-file diagnostic result. The new fixture has complete clean LSP diagnostics.

### September 21: opt-in dyadic API with closed canonical/raw bridges

The user required the raw-record API as default unless the dyadic API had an
explicit bridge or compelling separate purpose. `ComputableCompare` is now
an explicit opt-in import, retaining arbitrary-dyadic value comparison.
Four `SF*C_eq_raw_of_canonical` theorems prove equality to the raw comparator
on `BinarySingleNaNFloat prec emax`; eight typed-wrapper bridges follow.
All proofs are closed. The real-value argument relies on the existing
`Bcompare_correct` and checks special constructors separately. The proof-carrying
primitive wrapper really does provide canonical validity; the previous guide's
description of its projection as unconstrained is corrected.

Source fingerprint `7c2c0450413b76bf33303a2aa80f5da967ada72f39dd503e4cf3a022bcad79ed`
passes a full 6225-job build. Pure Lean runs 3364 canonical input pairs / four
comparisons each and 20000 existing dyadic pairs. Compiled trust explicitly
imports the opt-in module: 13743 declarations / 59 modules, the same four debts.
Fresh source metadata validates 344 anchors. The expanded `prim_comparison`
bridge observes 26 fields and passes 1345 cases in compiled/reduced Lean and
pinned Rocq, plus 1345 generated kernel equalities (seed 864101, 388.072 s).
Its six literal boundary clients and 24 individual API mutations pass in
82.663 s. The non-live harness reports 32 passed / 44 live tests skipped.

Receipts: `/private/tmp/floatspec-canonical-864101-v2/report.json`,
`/private/tmp/floatspec-canonical-live-mutations-v2-20260921.log`, and
`/private/tmp/floatspec-canonical-bridge-build2-20260921.log`.
The first expanded adapter used the wrong Rocq namespace for the imported
`B2SF`; it failed to compile. Its report remains `error` and its 25 test errors
are retained in the initial logs; only the corrected v2 runs are passes.
Hosted Linux builds are still pending, not claimed green.

The user also suggested a classical-use linter, then explicitly allowed
discarding it if unwise. No keyword ban was added: proof-only classical use
is legitimate, and the compiler/runtime gates are the relevant check for
executable declarations. `Print Assumptions` is an axiom audit, not a reliable
test of whether erased proofs prevent execution.

### September 21: actual dependency/declaration queue and first source slice

At the user's suggestion the audit now uses actual `coqdep` order and compiled
`.glob` declaration offsets. The tool validates the source pin, source digests,
dependency precedence, source anchors and manual-review references. It handles
same-token class facets and repeated scoped aliases; unknown metadata and
unsupported mutual blocks fail explicitly. The pin has 2716 declaration sites
across 35 modules. These include notations and generated proof infrastructure,
so they are not a missing-work denominator. Historical prose-ledger reviews
are not silently promoted into this new conservative manifest.

The first eight sites now have dispositions: seven reviewed contracts and one
adapted proof-infrastructure entry. Compiled direct type/body hashes and the
noncomputable flag make subsequent direct-declaration drift a review failure.
This is a noncryptographic change detector, not a transitive-dependency proof.
The first actual rewrite is `Core.Zaux.iter_pos`, whose three binary-positive
branches now match the imported Corelib body. The existing public
`iter_pos_nat` theorem is proved for all functions/counts/initial values,
preserving the former natural-iteration semantics. No source type was weakened.

Snapshot `55f57d905da2ac4ad0e58388cf227ac14bf34778d2e25cd3a6d1b8d3ccd29a9a`
passes the full macOS Lean 4.34 build (6225 jobs), compiled trust (13753 source
declarations / 59 modules / four debts), and 351 source anchors. Zaux and the
paired Lean fixture have complete clean LSP diagnostics. Both assistants check
the prelude's exact propositions, version 40202, dependent Boolean branches,
eight fixed iterations and fourteen sign cases. The new profile passes 1244
three-way executions, independent closed-form checks and generated kernel
equalities (seed 864211, 103.192 s). Four harness tests include two live mutations
applied to both assistants; their shared wrong results are rejected by the
oracle. Nine queue tests cover ordering, stale digests, metadata ambiguity,
review/candidate separation and unsupported mutual declarations.

Receipts: `/private/tmp/floatspec-zaux-prelude-864211-v2/report.json`,
`/private/tmp/floatspec-zaux-source-build-20260921.log`,
`/private/tmp/floatspec-zaux-trust-20260921.json`,
`/private/tmp/floatspec-source-queue-final-20260921.json`.
The first large prelude run lacked Lean's deep-term printing option: its
abbreviated output was rejected before comparison. That initial report remains
`error` with zero compared cases; the v2 run is the pass. Early queue generator
failures on real class facets and reused aliases were fixed and regression-tested.
Hosted Linux builds remain pending. The aggregate all-profile suite has not
been rerun on this snapshot; the new profile is integrated for future runs.

A fresh pinned-Rocq axiom probe confirms the computability distinction:
`Zfloor` depends on `ClassicalDedekindReals.sig_forall_dec`; `mag` also depends
on excluded middle and `sig_not_dec`. `SpecFloat.iter_pos` and `cond_Zopp`
are closed under the global context. Total logical definitions do not imply
an executable algorithm for arbitrary mathematical reals.

### September 21: hosted build succeeds, scanner prerequisite failure repaired

Run `35548504304` completed its Linux Lean 4.34.0 source build, saved a 1.46 GB
compatible action cache and passed the standalone regression step. It failed
at the next gate: `rg: command not found`. The placeholder scanner's `|| true`
had hidden the missing tool; its mutation fixture correctly rejected that
apparent empty scan. This was a runner/scanner failure, not a Lean failure.

The workflow now installs ripgrep before any expensive build. The scanner
accepts only ripgrep status 1 as an empty result, and fails on unavailable tools,
unreadable inputs or search errors. The mvcgen hygiene gate and workflow's Unit
placeholder query use the same fail-closed distinction. Five new tests inject
missing PATH tools, nonexistent input, statuses 2/127 and text-query failure,
while retaining passing empty/clean inputs. Existing real Lean placeholder
fixtures, unused-mvcgen gate and four-debt manifest scan also pass locally.
Hosted trust/status/hygiene stages were skipped in that run and remain unverified.
Receipt: `/private/tmp/floatspec-ci-35548504304-failure.log`.

### September 21: next twenty source sites, integer-power/radix contracts

The ordered review now reaches `Zpower_gt_id`: parity, integer power laws,
the radix record/projections and bounds. The direct Lean propositions already
match the source domains. The paired fixture makes the source Boolean/proof
adaptations explicit: `Z.even` versus decidable `Even`, and `Z.leb 2 value = true`
versus `2 ≤ value`. Manifest fingerprints include record constructor/field types
and the integer-power body where relevant, not merely the record's type name.
Eighteen new source anchors are validated against compiled source declarations.

Removed 38 unused named check/spec declarations from this reviewed prelude and
power slice. The actual mathematical laws and closed proofs remain unchanged.
Some wrappers only restated a definition, and one inversion wrapper carried a
wrong `natAbs` premise without proving the advertised exponent implication.
The remaining source-facing theorem uses actual integer `Zpower` and is correct.
Both assistants prove the counterexample `-2 < -1` with both integer powers zero;
the source's upper-exponent nonnegativity premise cannot be dropped.

Source snapshot `f2fb5d00c990e08667c278a1c831086e2b4e45f2b8b5a26a9437b5db99a99764`
passes full macOS Lean 4.34 (6225 jobs), complete LSP diagnostics, compiled trust
(13713 source declarations / 59 modules / the same four debts), and 369 anchors.
The queue has 28 explicit dispositions and 2688 unreviewed sites. Nine queue
tests pass, and the old review fingerprints still match.

Paired typed clients and eight live contract mutants pass (two unittest methods,
14.614 s). The first mutation run failed on a too-case-sensitive diagnostic regex,
not an accepted bad contract; its failure log is retained. The corrected run
requires the expected type/kernel diagnostic rather than accepting any process
failure. Fresh seed 864307 passes 228 power cases across compiled/reduced Lean
and pinned Rocq plus 228 generated kernel equalities (18.648 s). Three existing
live runner tests pass, including two actual wrong-program mutations (15.396 s).
The ordinary harness reports 32 passing tests and 44 skipped live tests.

Receipts: `/private/tmp/floatspec-zaux-power-build-20260921.log`,
`/private/tmp/floatspec-zaux-powers-864307/report.json`,
`/private/tmp/floatspec-zaux-power-mutations-v2-20260921.log`,
`/private/tmp/floatspec-power-live-runner-tests-20260921.log`,
`/private/tmp/floatspec-power-trust-20260921.json`,
`/private/tmp/floatspec-power-source-queue-20260921.json`.
No new proof debt or numerical operation rewrite was needed in this slice.
The full aggregate all-profile suite was not rerun; the new fixtures and tests
are integrated into its next run. Hosted follow-up CI is still pending.

### September 21: source division/remainder slice and signed rounding modes

Eight more source contracts, `Zmod_mod_mult` through `ZOdiv_plus`, now have
explicit dispositions and anchors. The existing direct propositions/proofs
were already correct. The source's two floor-style laws constrain divisors to
be nonnegative, where Lean's default Euclidean operations agree with floor
division. The paired fixture checks both universal Lean bridges and the
negative-divisor distinction: 7 divided by -3 is (-3,-2) in quotient/remainder
floor convention but (-2,1) in Lean's default convention. The six truncating
laws explicitly use `tdiv`/`tmod` and retain zero/negative cases. Both assistants
prove the genuine sign-premise counterexample for quotient addition at -2,1,2;
the Lean proof depends on no axioms.

Sixteen unused check/spec wrappers were removed after verifying no callers.
In particular the obsolete quotient-addition check used default division despite
its truncating name/docstring; the actual direct theorem remains unchanged.
This brings the reviewed-slice cleanup to 54 named wrappers, not 54 source laws.

Snapshot `949e91ee425bc4671889c457b0584aca10df459eab4fc3280384e73b75a71a01`
passes full macOS Lean 4.34 (6225 jobs), complete LSP diagnostics, paired 1377-
input signed grids, six live contract mutants (11.363 s), and fresh seed 864503:
811 compiled/reduced Lean versus Rocq floor-division calls and 811 generated
kernel equalities (54.986 s). The corpus includes 33 zero and 386 negative
divisors. A saved-output Python oracle independently checks all three observed
paths using floor division and exact reconstruction. The existing pure Lean
and pure Rocq ArithmeticProperties suites were also explicitly rerun.

Compiled trust observes 13695 declarations / 59 modules / the same four debts.
All 377 source anchors validate against compiled Rocq sites. The ordered queue
has 36 dispositions and 2680 unreviewed sites; the next is `Zsame_sign_trans`.
No arithmetic implementation or mathematical theorem type was changed, and no
new proof was deferred.

Receipts: `/private/tmp/floatspec-zaux-division-build-v2-20260921.log`,
`/private/tmp/floatspec-zaux-division-mutations-v2-20260921.log`,
`/private/tmp/floatspec-zaux-division-864503/report.json`,
`/private/tmp/floatspec-zaux-division-independent-oracle-20260921.log`,
`/private/tmp/floatspec-division-trust-20260921.json`,
`/private/tmp/floatspec-division-source-queue-20260921.json`.
The initial full build was interrupted to correct source-anchor line numbers;
it is not a pass. A premature test invocation failed on its missing rebuilt
Zaux object, and an extra Rocq-suite invocation failed because the requested
output basename differed from its source. Both were rerun successfully with
separate receipts. Initial fixture elaboration/notation errors were corrected
before any pass was recorded. Aggregate all-profile and latest hosted CI
success remain separate from these completed local/targeted checks.

### September 21, 02:37 UTC: complete hosted CI repair verified

GitHub run `35553327541` at commit `ca7eb4f7182547a727bf65e765a4f5434901e390`
completed successfully. All job steps passed: stable Lean 4.34.0 build,
standalone regressions, trust/placeholder tests, generated-status consistency
and source hygiene. Its Linux review-drift gate also validated the eight entries
present at that revision, providing a cross-platform check of their structural
hashes. The later audit revisions have additional entries and separate pending
runs; this green run is not attributed to them.

Receipt: `/private/tmp/floatspec-ci-35553327541-success.log` and
<https://github.com/alok/FloatSpec/actions/runs/35553327541>.
Hosted CI does not install/run the live Rocq profiles: their skipped live tests
are not passes, and the local pinned-Rocq/differential receipts remain separate.

### September 21, 17:55 UTC: port-completion focus, 25 direct rounding contracts

The user reaffirmed that completing the port is the main goal. Instead of
continuing Zaux wrapper cleanup, this slice restores the actual public
mathematical interface in `Core/Round_pred.v:89–539`: twenty new direct
exports and five repaired source-named exports that had still returned
Boolean/Hoare contracts. Existing wrapper proofs supplied most of the
mathematics; this is a source-API repair, not an arithmetic-algorithm repair.
The old `*_spec` compatibility API remains, with no callers of the five
changed interfaces found in repository source. All 25 reviewed laws retain
their exact source premises and have pinned links and closed Lean proofs.

Both assistants independently prove three counterexamples using format
`{−1, 1}`: nearest selection is not nonstrictly monotone or unconditionally
unique, and pointwise truncation is not monotone without zero membership.
Eight live contract mutations are rejected (two test methods, 14.960 s).
The first live harness attempt correctly failed on a Rocq deprecation warning;
the fixture now imports `Stdlib`, and the separately recorded rerun passed.
Initial fixture namespace and Rocq tactic/notation errors were corrected;
they were not counted as successful semantic tests.

Source snapshot `8b16a912af4114cd59820fd84582e56acca0945dfeee2a0ffde6476996a658de`
passes complete LSP diagnostics, the full macOS Lean 4.34 build (6225 jobs),
and fresh seed 865103: 3539 three-way executions plus generated kernel
equalities (279 `round`, 3260 `nearby`; 235.593 s). The executable bridge
is regression evidence for those algorithms, separate from the exact real-
predicate clients and universal Lean proofs. It does not execute arbitrary
real-valued specifications or establish whole-library source equivalence.

Compiled trust: 13720 source declarations / 59 modules / the same four named
debts. All 402 source anchors validate; 61 source sites now have explicit
manifest dispositions (first 36 contiguous sites plus these 25), with 2655
unreviewed sites. These are not missing-API counts or a completion percentage.
Review drift, nine queue tests, five fail-closed scanner tests, placeholder
gates, actionlint, shell syntax and unchanged generated-status checks pass.
Core harness: 76 tests, 32 passed and 44 unavailable live tests explicitly
skipped; the new paired live contract tests ran separately.

Receipts: `/private/tmp/floatspec-round-pred-build-20260921.log`,
`/private/tmp/floatspec-round-pred-contracts-20260921/lean.log`,
`/private/tmp/floatspec-round-pred-contracts-20260921/rocq.log`,
`/private/tmp/floatspec-round-pred-mutations-v2-20260921.log`,
`/private/tmp/floatspec-round-pred-865103/report.json`,
`/private/tmp/floatspec-round-pred-trust-20260921.json`,
`/private/tmp/floatspec-round-pred-queue-20260921.json`.

The hosted runs for `a0fd6e45`, `aeae41fa` and `20abab5e` were independently
observed green at 17:37 UTC. This new slice has not yet been observed green
on hosted CI. `Deps/flocq` and its seven untracked dpd artifacts are unchanged.
Next substantive port slice: remaining nearest/generic tie-policy interfaces,
then format-transfer and totality contracts; do not confuse a matching name
with a matching public proposition.

### September 21, 18:18 UTC: complete the public Round_pred interface

The second slice adds 33 direct laws and repairs the source-named generic
negation law, completing 59 direct theorem exports across the two slices.
Nearest sign/absolute-value laws, generic tie uniqueness, ties away/toward
zero, sign preservation and local format transfer now expose the actual
source propositions. Numerical operation bodies are unchanged; closed legacy
proofs are reused where faithful, and simpler laws compose direct proofs.
No new `sorry` or executable classical decision is introduced.

Paired Lean/Rocq clients also check the existing function liftings, dependent
witness constructors, format hypotheses, totality statements and generated
elimination interface. All 78 top-level source sites, the constructor and
four generated schemes have explicit manifest dispositions. Generated schemes
are adapted proof infrastructure, not identical Rocq proof terms. The witness
construction uses Lean's classical choice; its source-shaped dependent contract
does not claim that this is the same term as Rocq's completeness construction.
The manifest now has 114 reviewed contracts and five infrastructure adaptations;
2597 source sites remain unreviewed by that manifest. Earlier prose reviews
are not silently reclassified, and these counts are not a completion fraction.

Both assistants prove that the format `{−1, 1}` defeats uniqueness for both
zero-directed tie policies without zero membership. Another exact client
checks the permitted always-false generic policy at representable inputs.
The auxiliary uniqueness condition's Type-valued domain is preserved separately
from the Prop-valued actual rounding relation. The source's explicit `F 0`
premise for `satisfies_any_imp_N0` remains, even though it is also derivable.
Twenty live premise/conclusion mutations across four methods pass their positive
controls and are rejected (38.006 s). Initial fixture failures involving an
implicit constructor parameter and a Rocq policy inferred as Type instead of
Prop were corrected before the recorded successful runs; failures are not passes.

Verified snapshot:
`8aa8e9e323ead2804b7e839e6a350a591d4bcdfa3ea66032c148342ed4fddf27`.
Complete LSP diagnostics, full macOS Lean 4.34 build (6225 jobs), compiled trust
(13774 source declarations / 59 modules / four unchanged debts), all 453 source
anchors, all 119 compiled review fingerprints, nine queue tests, placeholder
gates, actionlint, shell syntax and unchanged generated status pass.
Fresh seed 865307 passes 3260 three-way cases and bootstrapped kernel equalities
(140 `round`, 3120 `nearby`; 242.362 s). This profile compares compiled Lean,
Lean reduction and pinned Rocq; it has no separate independent rational oracle.
It is finite arithmetic regression evidence, not execution of arbitrary reals
or a universal predicate/source correspondence certificate.

Receipts: `/private/tmp/floatspec-round-pred-complete-build-20260921.log`,
`/private/tmp/floatspec-round-pred-ties-20260921/lean.log`,
`/private/tmp/floatspec-round-pred-ties-20260921/rocq.log`,
`/private/tmp/floatspec-round-pred-complete-mutations-20260921.log`,
`/private/tmp/floatspec-round-pred-865307/report.json`,
`/private/tmp/floatspec-round-pred-complete-trust-20260921.json`,
`/private/tmp/floatspec-round-pred-complete-queue-20260921.json`.

The first slice is pushed as `60096e0c`. Its hosted run `35635101867` passed
the stable Lean 4.34 build at 18:10 UTC; later steps were still running when
this entry was written. The second slice has local evidence, not yet a hosted
CI pass. The user's `Deps/flocq` state and seven untracked artifacts are unchanged.

### September 21, 18:31 UTC: direct nearest-even totality and monotonicity

The next concrete source-API gap was `Round_NE.v:263,306,331`. Totality,
monotonicity and the combined rounding contract still used source names for
Boolean/Hoare interfaces. They now export the actual propositions, keeping
`Valid_exp` and `Exists_NE`, without adding `Monotone_exp`. `ValidRadix`
supplies the source's structured-radix invariant; an extra explicit `beta > 1`
is unnecessary. Compatibility proofs remain under `*_spec`; local consumers
use the direct laws, and an obsolete private unpacking helper is removed.
No numerical definition, tie policy or proof-debt obligation changed.

The paired nearest-even fixture now checks seven exact interfaces and proves
a short composition example: ordering exact inputs orders their actual
nearest-even rounded values. Eight live mutations reject missing format/parity
premises, a bare-existence replacement for a concrete result, and confusing
totality with the combined total/monotone contract (36.398 s, final fixtures).
All listed Lean theorem dependencies are standard axioms, with no `sorryAx`.
The Rocq assumption report is retained separately; no claim of axiom-free or
identical cross-system foundations is inferred.

Final snapshot:
`cd22873cb11cf2d8f72aa29e9050b8888aff63c8debbf1ca62d19642314626dd`.
The final full macOS Lean 4.34 build passes 6225 jobs, after the compatibility
docstrings were clarified. Compiled trust passes 13778 source declarations /
59 modules / four unchanged debts; 456 anchors validate, and the three new
review entries bring the manifest to 122 (117 contracts, five infrastructure
adaptations, 2594 unreviewed sites). Placeholder/linter guards, generated status,
actionlint and source hygiene pass. This follow-up has no newly recorded
differential bridge run: numerical definitions are unchanged, and the preceding
3539/3260-case receipts retain their own source fingerprints.

Receipts: `/private/tmp/floatspec-ne-totality-final-build-20260921.log`,
`/private/tmp/floatspec-ne-totality-contracts-20260921/lean.log`,
`/private/tmp/floatspec-ne-totality-contracts-20260921/rocq.log`,
`/private/tmp/floatspec-ne-totality-contracts-final-20260921.log`,
`/private/tmp/floatspec-ne-totality-trust-20260921.json`,
`/private/tmp/floatspec-ne-totality-queue-20260921.json`.

Hosted CI `35635101867` at the first slice `60096e0c` completed fully green
at 18:23 UTC: stable Lean 4.34 build, regressions, trust, generated status and
hygiene. The later `a3a84b81` run and this follow-up require their own receipts.
One GitHub status request hit a TLS handshake timeout; that is an observation
failure, not a failed CI job or a passing result. `Deps/flocq` is unchanged.

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
