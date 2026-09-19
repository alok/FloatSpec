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

See [the three-loop guide](THREE_VERIFICATION_LOOPS.md) for commands, output
artifacts, and current coverage. No source algorithm was changed to make these
new tests pass; the substantive repair so far is the source-link linter gate.

## Execution priorities

Maintain three separate loops: independent Lean tests, independent pinned
Flocq/Rocq tests, and a differential bridge that sends identical inputs to both.
Record concrete cases and seeds; promote disagreements to permanent regression
examples. Keep valid theorem domains distinct from total-function behavior
outside those domains. Test the bridge with intentional mismatches so a parser
or skipped command cannot silently produce a green result.

## Still unreviewed

The bulk of the theorem-by-theorem port and prior changes remain unreviewed.
Next work includes executable arithmetic/rounding cross-tests, the trust and
source-anchor scanner boundaries, and source-signature checks informed by any
counterexamples. Passing compilation, finite agreement, and a proof of a Lean
statement are three different claims; none alone proves whole-library Flocq
equivalence.
