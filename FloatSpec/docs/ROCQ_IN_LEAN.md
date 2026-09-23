# Compiling Rocq into Lean: what it would take (and what Flocq needs)

*2026-09-22. Flocq 7aab8f55 (upstream https://gitlab.inria.fr/flocq/flocq), built under Rocq 9.1.0 with `~/FloatSpec/_opam/bin/coqc` (Flocq `config.log:104`; the `coqc` on PATH is Homebrew Rocq 9.2 and was not used). Lean v4.34.0 and v4.35.0-rc2; Mathlib 85e3a25e00, the version FloatSpec pins.*

*Evidence. The raw measurements (coq-dpdgraph closures, `Print`/`About`/`Print Assumptions` dumps, VM-cast counts, benchmarks) and the guided demo files were produced in a scratch session and are summarized here; that scratchpad will not persist. "Demo Gn" means section n of the scratch file `RocqGapsDemo.lean` (Lean v4.34.0, no Mathlib, every `#guard_msgs` passing). File:line citations point into Flocq 7aab8f55, the Rocq 9.1.0 Corelib/Stdlib under `~/FloatSpec/_opam/lib/coq`, and Lean at tag v4.34.0 unless stated otherwise. An adversarial fact-check has been applied; see the last section.*

## 1. Bottom line

1. Coinduction does not block Flocq. Its full kernel dependency closure has 7,631 objects, including 116 inductive types. None of them is coinductive and none uses `cofix`. Excluding `IEEE754/PrimFloat.v`, the closure depends on four axioms, all available in Lean. `PrimFloat.v` adds 58 more assumptions (float64/int63 primitives and their specification axioms), for 62 in total.
2. The real costs are elsewhere:
   - universes: Prop ≤ Type cumulativity and template polymorphism;
   - compiling Rocq `fix` into Lean recursors, including at least one Stdlib definition that only Rocq's guard checker accepts, over an inductive with a non-uniform parameter;
   - flattening functors and sealed modules;
   - re-checking about 3,751 VM-cast proof steps across the closure, 2,961 of them in Flocq's own declarations. On one microbenchmark with a hand-built encoding, Lean's kernel was about 20–40× slower than Rocq's lazy kernel and about 1,000× slower than Rocq's VM; the elaborator-compiled version timed out.

   Even after all of that, the output is useful to FloatSpec only once translated Rocq `R`/`Z` are aligned with Mathlib's `ℝ`/`ℤ`.
3. I found no mechanical Rocq→Lean kernel translator. The one direct kernel-level bridge between the two systems, rocq-lean-import, goes Lean→Rocq, and existing Rocq→Lean work is LLM-based. The smallest honest demo is Flocq's executable integer layer (`Zfast_pow_pos` closes over only 17 objects), checked against FloatSpec through the existing bridge. The binary-float layer is the natural next step, but its closure already reaches the reals (§6).

## 2. What Flocq actually uses (census)

| Feature | Flocq 7aab8f55 and its closure | Where |
|---|---|---|
| Size | 34 `.v` files (63,149 lines) and 2,547 declarations. Loading every module pulls in 362 libraries: 44 Corelib, 283 Stdlib and 35 Flocq (including the generated `Version.v`). An earlier run counted 357. | `Print Libraries` |
| Kernel closure | 7,631 objects: 7,259 constants, 116 inductives and 256 constructors; 5,731 of them are proofs (Prop-typed). Computed as the union of coq-dpdgraph `Print DependGraph` over every declaration. None of the 116 inductives is coinductive or mutual. | coq-dpdgraph |
| Coinduction | Flocq has 0 `CoInductive`, `CoFixpoint` or `cofix`. The loaded libraries have 4 non-recursive marker Props, none reachable from Flocq. | Corelib `Classes/Morphisms.v:306,540`; `CMorphisms.v:237,482` |
| Recursion | 12 `Fixpoint`s, all structural on `positive`, `nat` or `list`. Two more `fix` uses: `Even_Odd_double` is built with the `fix` tactic (recursion on n−2), and `Version.v`'s `let fix parse` is removed by `Eval vm_compute` before the kernel sees it. No `Program`, `Equations`, `Function`, `Fix_F` or `Acc`. | `Zaux.v:824,862,980`; `Digits.v:33,260,728`; `Pff.v:37,542,630,1968,2050,5337,5854` |
| Recursion in the closure | Mutual: `Pos.add` with `add_carry`, and `sub_mask`. Nested: `ZArithProof` with `ZChecker`. At least one definition that only the guard checker accepts: `linear_search_conform`. Nobody has exhaustively scanned the closure's `fix` terms. Its inductive `before_witness (n:nat)` also has a non-uniform parameter: it recurses at `S n`. | `PosDef.v:68,135,147`; `ZMicromega.v:564,1017`; `ConstructiveEpsilon.v:121-123,155-166` |
| Universes | Flocq has 0 `Polymorphic` or `Cumulative` declarations. It has only a handful of monomorphic levels of its own, out of 1,334 global levels after loading; about 7 can be identified, such as `binary_float_rect.u0`, `mode_rect.u0` and `Iter.u0`. It relies on Prop ≤ Type in `eqbool_irrelevance`, which passes the Prop-valued `eq true` to `eqbool_dep : forall P : bool -> Type, …`. The closure has 15 template-polymorphic inductives (44 objects counting constructors): `prod`, `list`, `option`, `sum`, `sig`, `sigT`, `sumor`, `eq` and `ex`, plus `EnvRing.PExpr`, `EnvRing.Pol`, `RingMicromega.Formula`, `VarMap.t`, `ZifyClasses.InjTyp` and `SetoidTactics.DefaultRelation`. It also has 37 universe-polymorphic objects: 21 from CRelationClasses, 15 from CMorphisms and 1 (`Unconvertible`) from Corelib `Classes/Init`. The CRelationClasses ones include the polymorphic inductive `Equivalence` and its constructor. | `Zaux.v:51-68`; `Datatypes.v:202,222,248,318`; `Specif.v:29,44,924`; `Logic.v:274,378` |
| Opacity | 2,065 opaque and 455 transparent declarations. 11 are built by tactics and closed with `Defined`, such as `Bldexp`, `Bsucc` and `Bpred`. 8 are data but closed with `Qed`: `LPO`, `LPO_Z`, `LPO_min`, `mag`, `round_fun_of_pred`, `round_val_of_pred`, `OddEvenDec` and `floatDec`. | `Binary.v:533-1426`; `Raux.v:1588` |
| Reflexive proofs | Flocq's own declarations contain 2,961 VM casts (`eq_refl <: …`), spread over 823 of them. 596 declarations reference `ZTautoChecker_sound` (from `lia`) and 62 reference `RTautoChecker_sound` (from `lra`). The rest of the closure adds 790 VM casts in 263 Stdlib/Corelib declarations, for example in ConstructiveCauchyReals, Uint63 and QArith_base. The closure total is about 3,751 casts in about 1,086 declarations. Casts come from `… = true` checkers, and also from `ring` (`Ring_polynom.mk_monpol_list`, `norm_subst`, `Peq`) and `field` (`Fnorm`). There are 0 native casts. | counted from `Print` output |
| Modules | Flocq itself has only 2 plain modules. The closure needs functors flattened: `Z.le_trans` comes from `Include ZBasicProp`. It also needs sealing: the reals sit behind `RbaseSymbolsImpl : RbaseSymbolsSig`. | `BinInt.v:524`; `Rdefinitions.v:38-88,195-211` |
| Elaboration | 7 classes, 28 instances, 74 coercions, 0 canonical structures, 5 Ltac definitions and 209 sections. Instance search, coercion insertion, Ltac and section discharge all finish before the kernel runs. The classes and instances still reach the kernel, but only as ordinary records and constants. | — |
| Primitives | Only `IEEE754/PrimFloat.v` uses them (float64 and int63). `Print Assumptions` lists 18 PrimFloat and 10 PrimInt63 primitives, plus 20 FloatAxioms and 10 Uint63Axioms. No PArray and no `native_compute`. | `PrimFloat.v:24-25`; `FloatAxioms.v:27-69` |
| Axioms | Excluding `PrimFloat.v`, the axioms are `classic`, `functional_extensionality_dep`, `sig_forall_dec` and `sig_not_dec`. Over the whole bundle, `Print Assumptions` lists 62 assumptions: these 4 plus the 58 primitives and float/int axioms above. I sampled 15 headline declarations: 12 depend on exactly the four, 1 on a subset (`sig_forall_dec` and funext), and 2 from `PrimFloat.v` also on primitives. | `ClassicalDedekindReals.v:110,115` |
| Absent | Primitive projections, impredicative Set, rewrite rules, `Unset Guard Checking`. SProp appears only in 21 auto-generated `*_sind` eliminators, such as `FIX_format_sind` and `BinarySingleNaN.binary_float_sind`. These can be mapped to Prop or dropped. | — |

## 3. Kernel gaps that matter, ranked

| # | Gap | Verdict | Flocq exposure | Workaround |
|---|---|---|---|---|
| 1 | Alignment. Translation produces new Lean types for Rocq's `R`, `Z` and `positive`, not Mathlib's `ℝ`/`ℤ`. | Blocks usefulness, though not kernel checking | Every real-valued statement. `mag` alone closes over 4,153 objects, including `ln`, `exp`, IVT, MVT and the Cauchy reals (`CReal`). | Mathlib's `inducedOrderRingIso` (`Mathlib/Algebra/Order/CompleteField.lean:284`) applies once translated `R` is shown to be a `ConditionallyCompleteLinearOrderedField`. Both libraries set `Rinv 0 = 0` (`Rdefinitions.v:196-200`). Alternatively, stop translating at `RbaseSymbolsSig` or the RIneq layer and supply those lemmas from Mathlib. |
| 2 | VM-reflexive proofs. Lean's kernel has no VM and only accelerates `Nat` (`type_checker.cpp:702`), while Rocq's `positive`/`Z` are binary inductives. | Complication; may be a practical blocker | About 3,751 casts in about 1,086 closure declarations (2,961 of them in 823 Flocq declarations). The microbenchmark was `Pos.eqb (3^n) (3^(n/2) * 3^(n/2))` at n=3000 on Rocq-style binary `positive`. Rocq's VM took 0.21–0.22 s and its lazy kernel 6.9–7.0 s. Lean's kernel took 225 s on a hand-built `Pos.rec` encoding with `maxHeartbeats 0`; a rerun under load took 196 s of user time. Compiled by Lean's structural-recursion elaborator instead, the same function hit `(kernel) deterministic timeout` at default heartbeats. | Re-prove these statements with `omega`/`linarith`/`ring`/`grind` instead of translating the terms. `native_decide` has added one fresh axiom per use since v4.29.0 (lean4 PR #12217). |
| 3 | Universes: cumulativity, template polymorphism, and polymorphism with level constraints. Lean compares sorts by equality (`type_checker.cpp:844`). Lean's *elaborator* rejects an inductive whose sort is `Sort (max u v)` (`MutualInductive.lean:1128`). The kernel accepts one added directly with `addDecl`, but its recursor then eliminates only into Prop (`inductive.cpp:522-538`). So a translated template `prod` would type-check but could not be eliminated into data. | Complication | Small: Prop ≤ Type in `eqbool_irrelevance`, 15 template-polymorphic inductives such as `prod`/`list`/`option`, and 37 universe-polymorphic setoid objects. | Universe-polymorphic elaboration (Felicissimo–Blanqui, LMCS 2024). Specialize per sort (`And`/`PProd`/`Prod`). Use `PLift`/`ULift` only where a strict `≤` is really used; `ULift` is not local, since it does not commute with Π definitionally (Assaf, TYPES 2014). Duplicate constants where one level substitution cannot cover every use. |
| 4 | Rocq's kernel has a `fix` term; Lean's has none (`expr.h:84`), only recursors. | Complication | Structural, mutual and nested recursion, plus at least one exception. `linear_search_conform` returns data by recursion on the two-constructor Prop `before_witness`, and Lean only lets a subsingleton Prop eliminate into data (`inductive.cpp:522`). `before_witness (n:nat)` also recurses at `S n`. Lean rejects that non-uniform parameter (`inductiveParamMismatch`), so it must become an index. | Compile `fix` to `rec`/`brecOn` by replaying Rocq's guard evidence. Nested types go through Lean's auxiliary-mutual encoding (`inductive.cpp:985`). Turn non-uniform parameters into indices. Rewrite `linear_search_conform` by hand using `Acc` or a classical `Nat.find`. Well-founded recursion is a fallback. The elaborator treats `WellFounded.fix` as irreducible, so its equations hold only propositionally there, but the kernel still unfolds it on closed terms (`decide +kernel` evaluates `half₂ 10`, demo G5). |
| 5 | Modules. Rocq's module system is in its kernel; Lean's kernel has none. | Complication | Stdlib functors (`Include`), and three sealed modules: the reals, `RinvImpl` and `PrivateImplementsBitwiseSpec`. | Flatten functor instances and turn sealed fields into Lean `opaque`. |
| 6 | Primitive float64/int63 values | Complication, isolated | Only in `PrimFloat.v`, but it contributes 58 of the 62 assumptions. | Map them to Lean's `Float.Model` (lean4 PR #14079, first in v4.33.0-rc1) and prove Rocq's `FloatAxioms` as theorems, or leave `PrimFloat.v` out of scope. |
| 7 | Opaque data. A Lean `theorem` must have a Prop type. | Minor | 8 declarations, including `mag` and `round_val_of_pred`. | Translate them as `opaque` or as irreducible noncomputable definitions. |

These need no work for Flocq. On everything Flocq uses, Lean's rules match Rocq's or are more permissive:
- **Large elimination from Prop.** For every inductive in Flocq's closure, Lean's rule is at least as permissive; demo G3 shows a case Lean allows and Rocq refuses. This does not hold in general. Rocq lets mutual singleton Props eliminate into Type (`C_rect : forall P : Type, …`), while Lean restricts mutual inductive predicates to Prop (`inductive.cpp:529-531`). None of the 116 closure inductives is mutual, so Flocq is unaffected.
- **SProp and Prop.** Both become Lean `Prop` (`type_checker.cpp:932`), which also covers the 21 `*_sind` eliminators.
- **Record eta** (`:889`).
- **`Qed` opacity.**
- **The four logical axioms.** They reduce to `[propext, Classical.choice, Quot.sound]` (demo G10). The primitive-float assumptions are gap 6.

One theoretical caveat: Lean's algorithmic definitional equality is not transitive (Carneiro's thesis §3.1.1). Nothing measured here shows this affecting translated Rocq terms.

## 4. Coinduction specifically

**What Lean has, up to v4.35.0-rc2.**
- **Kernel:** nothing. A grep of `src/kernel` finds no coinductive support, and the manual says type theory lacks it (`Manual/RecursiveDefs/CoinductivePredicates.lean:31`).
- **Core Lean has coinductive predicates only:**

  | Feature | Lean PR | First release |
  |---|---|---|
  | `greatest_fixpoint` | #8097 | v4.20 |
  | renamed `coinductive_fixpoint` | #8948 | v4.22 |
  | mutual principles | #9358, #9628 | v4.23 |
  | `coinductive` command | #10333 | v4.25.0 |
  | `monotonicity_by` | #14861 | v4.35.0-rc1 |
  | `strong_coinduct` | #14855 | v4.35.0-rc1 |

  - **How it is built.** A `coinductive` predicate is a least fixpoint (`lfp_monotone`) in the reverse-implication order, over a generated non-recursive `_functor` inductive (`src/Lean/Elab/Coinductive.lean:21-95`).
  - **Consequences.** Its constructors are Prop-typed `def`s, not kernel constructors, and `coinduct` is a theorem. Unfolding goes through `functor_unfold`, not `rfl`. The predicate depends on `Classical.choice`.
  - **Data is rejected.** `coinductive CoStream (α : Type) : Type` fails with "can only be used to define predicates" (`MutualInductive.lean:1448-1450`, v4.34.0).
- **Coinductive data exists only in libraries:**
  - **Mathlib:** `Stream'`, `Seq` and `Computation`, plus `PFunctor.M`, where `M.dest (M.corec g x)` reduces by `rfl`, and `QPF.Cofix`.
  - **QPFTypes `codata`:** a proof of concept on toolchain v4.25.0, with no mutual or indexed families.
  - **ISTA-PLV/coinductive:** targets v4.34.0 and uses `partial_fixpoint`. It has no guardedness check and is classical throughout. Its stream test notes that `#eval zeros.stake 0` crashes Lean (`Test/Stream.lean:190-192`), though the interaction-tree `#eval`s in `Test/ITreeEval.lean` run.
  - **The FRO roadmap:** Year 4-1 (Sep 2026 – Feb 2027) does not mention coinduction.

**How Rocq constructs would map:**

| Rocq | Lean target | What is lost |
|---|---|---|
| Recursive `CoInductive P : … -> Prop` | `coinductive` or `coinductive_fixpoint` | `cofix` proofs must be rewritten against `P.coinduct` with a hand-chosen invariant. Unfolding becomes propositional, and the definition becomes classical. |
| Non-recursive `CoInductive … : Prop` (Corelib markers) | plain `inductive` | Nothing, since the greatest and least fixpoints coincide. |
| `CoInductive T : Type` with `CoFixpoint` | `PFunctor.M`, `Stream'`, `Seq`, `QPF.Cofix` or ISTA `CoInd` | Rocq's definitional cofix-under-`match` reduction, except for `M.dest ∘ corec` and `Stream'`. Indexed and mutual codata are unsupported. The translator has to insert rewrites. |

**Does it matter for Flocq?** No.
- Flocq and everything reachable from it contain no coinduction (§2). The four Corelib markers would be plain `inductive`s even if they were reachable.
- Coinduction does matter for CompCert-class developments. CompCert (master bd2b3826, 2026-09-17) uses `CoInductive` in 7 files:
  - `common/Events.v`, `common/Smallstep.v` and `common/Determinism.v`;
  - `backend/Cminor.v`, `cfrontend/ClightBigstep.v` and `cfrontend/Cstrategy.v`;
  - `MenhirLib/Interpreter.v`.

  9 files use `CoInductive`, `CoFixpoint` or `cofix`. The coinductive types include `traceinf` (data, `common/Events.v`), `forever` (a predicate, `common/Smallstep.v`) and MenhirLib's parser `buffer` (data). Coinductive data has no core-Lean target.
- In 2020 Gaëtan Gilbert (Rocq kernel developer) called Coq→Lean "way harder due to universe cumulativity (I wouldn't be surprised if it's impossible)". The same post lists non-uniform parameters among the obstacles and puts coinductives under "less used" (Lean Zulip, 2020-01-28, [thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Coq.20as.20a.20lean.20type.20checker/near/186831409)).

## 5. Prior art

| Tool | Direction and fragment | Coinductive support | Status | Link |
|---|---|---|---|---|
| rocq-lean-import (Gilbert) | Lean→Rocq kernel terms, read from lean4export output. The Mathlib figures in its README are for **Lean 3** mathlib exported with `lean --export`: 66,400 entries, 11,867 skipped (the first is `real.linear_order._proof_5`). That run used `Unset Conversion Checking` and a 10 s timeout, so it is not a kernel-checked import. | n/a, since Lean has none | Its README says experimental alpha. Last push 2026-09-11. | https://github.com/rocq-community/rocq-lean-import |
| CoqInE | Rocq `.vo` → Dedukti, for a large subset of CIC | Explicitly unsupported: `src/terms.ml:643` raises `not_supported "CoFix"`. Lines 641-647 also reject primitive Int, Float, Array and String. | last push 2025-09-04 | https://github.com/Deducteam/CoqInE |
| Logipedia | Dedukti → Lean and others, for the STT∀ fragment only. The Lean exporter emits Lean 3 syntax. | no | last push 2024-11; the site was unreachable when checked | https://github.com/Deducteam/logipedia |
| Predicativize | Matita → Agda through universe-polymorphic elaboration | no | research prototype (CSL 2023, LMCS 2024) | https://github.com/Deducteam/predicativize |
| hol2dk / coq-hol-light | HOL Light → Rocq; the Multivariate library, over 20k theorems | n/a | coq-hol-light 3.0.0 released 2025-01-21; hol2dk's latest release is 2.1.0 (2025-11-20); alignment paper arXiv 2609.24598 | https://github.com/Deducteam/hol2dk |
| Lean4Less | Lean → Lean−, removing proof irrelevance and K by inserting casts | n/a | handles stdlib and lower Mathlib; runs out of memory higher up (ICTAC 2025) | https://github.com/Deducteam/Lean4Less |
| Mathport (binport + synport) | Lean 3 → Lean 4, kernel terms plus syntax | n/a | port declared complete 2023-07-16; repo last pushed 2024-11-21, now archived | https://github.com/leanprover-community/mathport |
| lf-lean (Theorem) | LLM Rocq→Lean of Software Foundations vol. 1 (1,276 statements). Isomorphisms are checked in Rocq by round-tripping through rocq-lean-import. | the fragment has none | 97% autonomous, Jan–Feb 2026 | https://theorem.dev/blog/lf-lean/ |
| Babel-formal | LLM translation with proof terms as the pivot, on 117 lemmas. Rocq→Lean succeeds on 83.7% of lemmas across all runs combined. | n/a | NeurIPS 2025 MATH-AI | https://github.com/LLM4Rocq/babel-formal |
| Vero | LLM agents with human review. Its `flocq` instance has 73 APIs and 203 specs, from the same commit 7aab8f55. | n/a | arXiv 2608.13522 | https://github.com/sunblaze-ucb/vero |
| FloatLib | A Lean floating-point library of 1,242 files: arbitrary-precision IEEE binary and decimal formats, posits and P3109. Its `FloatLib/Floats/Formats/Flocq` subtree (41 files) follows Flocq's organization. It cites FloatSpec but does not depend on it. | n/a | arXiv 2609.19352 | https://github.com/lean-dojo/FloatLib |

ITPEval (arXiv 2607.19407) finds that library mismatch is the dominant bottleneck in LLM translation between provers. Its best pass@1 is 29.1% for statements and 10.5% for proofs.

## 6. A realistic plan

The design is to translate elaborated kernel terms, not tactic scripts, and let Lean's kernel be the checker. Every milestone is differentially tested against Rocq execution and against FloatSpec, using the existing shared-input bridge (`scripts/flocq_bridge.py`, `bash scripts/test_flocq_conformance.sh`; see `FloatSpec/docs/THREE_VERIFICATION_LOOPS.md`).

- **M0: integer slice (the smallest demo).**
  - *Translate:* Rocq's `positive`/`N`/`Z` with the mutual `Pos.add`/`add_carry` (`PosDef.v:68`), and Flocq's `Zaux`/`Digits` fixpoints such as `Zfast_pow_pos` (`Zaux.v:824`), which closes over only 17 objects.
  - *Exercises:* `fix`→recursor compilation, mutual recursion, and template polymorphism.
  - *Exit:*
    - the terms kernel-check in Lean;
    - their outputs match Rocq and FloatSpec's hand port (`FloatSpec/src/Core/Zaux.lean`) on the bridge's shared inputs;
    - translated `Z` is proven ≃ `Int`, as the first alignment.
- **M1: executable binary layer.**
  - *Translate:* the data definitions of `BinarySingleNaN`/`Binary`, including the `Defined` operations `Bldexp`, `Bfrexp`, `Bulp`, `Bsucc` and `Bpred`.
  - *Proof subterms:* the proof parts of values, such as boundedness witnesses, first become named, listed stubs that `#print axioms` shows. Without stubs, this slice drags in most of the real-number stack (see Risks).
  - *Exit:* bit-for-bit agreement with Rocq on the bridge's inputs.
  - *Why it matters:* FloatLib reports that FloatSpec's `Bplus`/`Bmult`/`Bdiv`/`Bsqrt` are `noncomputable` (as of FloatSpec revision 158263e). This milestone would give FloatSpec a computable reference to test against.
- **M2: statements, not proofs.**
  - *Translate:* Flocq theorem *types*, stopping at `RbaseSymbolsSig`/RIneq with `R ↦ ℝ`.
  - *Check:* each against FloatSpec's hand-ported statement, by `Iff`/`Eq` lemmas.
  - *Why it matters:* this makes today's manual source-faithfulness audit mechanical. For FloatSpec it is the highest-value milestone.
- **M3: proofs.**
  - *Translate:* the proof terms of the 1,724 Flocq declarations without VM casts. They still depend on the 263 Stdlib/Corelib declarations that contain the closure's other 790 casts.
  - *Re-prove:* with Lean tactics, the reflexive steps in the other 823 Flocq declarations and in those 263 Stdlib/Corelib declarations. Alternatively, supply the Stdlib lemmas from Mathlib.
  - *Handle by hand:* `linear_search_conform` and its non-uniform `before_witness`.
  - *Exit:* `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. This holds for the closure without `PrimFloat.v`, or with it once FloatAxioms and Uint63Axioms are proved about Lean models (gap 6).

**Risks**
- **Proof fields reach the reals (measured).** `binary_normalize` builds its result as `SF2B _ (proj1 (binary_round_correct …))` (`BinarySingleNaN.v:1751-1756`).
  - dpdgraph on `BinarySingleNaN.Bplus` gives 4,622 objects, including `R`, `Rplus`, `B2R` and `round`.
  - On `Binary.Bldexp` it gives 4,638.
  - So unless proof fields are stubbed, M1 pulls in about 60% of the 7,631-object closure. M0's `Zfast_pow_pos` needs 17 objects.
- **VM-cast cost is unmeasured on real `lia` witnesses.** The microbenchmark is one workload. On the hand-built `Pos.rec` encoding, Lean's kernel was about 20–40× slower than Rocq's lazy kernel, and the elaborator-compiled version timed out.
- **Output may grow.** Duplicating constants for universe instances could blow up the output, as it does in rocq-lean-import. The output will also not be idiomatic, as in the Metamath→Lean experience: definitions stay duplicated until they are aligned.
- **Alignment effort may dominate.** Mathport's effort went into `#align`, and ITPEval blames library mismatch.
- **Overlap with Vero and FloatLib.** The differentiator has to be a checked link back to the Rocq kernel terms, not coverage.

## 7. Slide-ready bullets ("future directions")

- **Compile Rocq into Lean.** No mechanical Rocq→Lean translator exists today: rocq-lean-import goes Lean→Rocq, and Rocq→Lean work is LLM-based. For Flocq, coinduction is *not* the obstacle, because its 7.6k-object kernel closure contains no coinductive type and no `cofix`.
- **The real costs:**
  - Rocq's universe cumulativity and template polymorphism;
  - `fix`→recursor compilation, plus a guard-checker-only Stdlib definition with a non-uniform parameter;
  - sealed Stdlib modules;
  - about 3.75k VM-checked `lia`/`lra`/`ring`/`field` steps across the closure, which Lean's kernel replays far more slowly.

  After that comes aligning Rocq `R` with Mathlib `ℝ`.
- **First slice:**
  - Mechanically translate Flocq's executable integer layer, then its binary-float layer.
  - Kernel-check both in Lean, and differential-test them against FloatSpec through the existing Rocq↔Lean bridge.
  - Then translate theorem *statements*, to check the port's faithfulness mechanically.

  Coinduction becomes the gap only for CompCert-class codata such as `traceinf`.

---

**Guided demo (Rocq source quoted in doc comments).**
- **Where it lives.** The scratch session produced the demo files listed below. The fact-check re-ran every one of them on its stated toolchain, and all passed. They live in the non-persistent scratchpad and have not been copied anywhere durable.
- **`RocqGapsDemo.lean`:** sections G1–G10, one per gap. Each section quotes the Rocq code in `/-! … -/` or `/-- … -/` comments. It runs on Lean v4.34.0 without Mathlib.
- **A matching Rocq file** with the same snippets, compiled under Rocq 9.1.0.
- **Coinduction demos**, which quote `Streams.v` with line numbers:
  - v4.34.0;
  - v4.35.0-rc2;
  - Mathlib;
  - ISTA-PLV/coinductive;
  - a Rocq counterpart.
- **An audit script** that reproduces the no-coinduction result for Flocq.

Rocq excerpts still worth adding as doc comments:
- `Zaux.v:53-58` (`eqbool_dep`) and its use at `:62`;
- `ConstructiveEpsilon.v:121-166` (`before_witness`, `inv_before_witness`, `linear_search_conform`);
- `ZMicromega.v:564-572` and `~1061`;
- `PosDef.v:68`;
- `Rdefinitions.v:38-66`;
- `Raux.v:1583-1588`;
- `BinarySingleNaN.v:1751-1756` (`binary_normalize`'s proof field);
- the VM-cast shape `ZTautoChecker_sound __ff __wit (eq_refl <: ZTautoChecker __ff __wit = true)`.

**Numbers note.**
- **Closure size:** two independent closure runs gave 7,631 and 7,633 objects. They started from 2,547 and 2,608 Flocq objects respectively.
- **Library counts:** 362 libraries (44 Corelib, 283 Stdlib, 35 Flocq) on the verified run; an earlier run counted 357.
- **Primitive and axiom counts:** these follow `Print Assumptions` over the whole bundle: 18 PrimFloat, 10 PrimInt63, 20 FloatAxioms and 10 Uint63Axioms. Earlier source-level counts differed by one.
- **VM casts:** the counts are a heuristic over `Print` output: 2,961 in Flocq's declarations plus 790 in the rest of the closure.
- **Lean source line numbers** refer to tag v4.34.0.
- **lf-lean size:** its blog says about 25k lines of Lean and 215k lines of Rocq.

## Corrections applied after fact-check

**Material (section A of the fact-check):**
1. **Axioms.** The "four axioms" claim now applies only to the closure without `PrimFloat.v`. The full bundle has 62 assumptions: 4 logical axioms, 20 FloatAxioms, 10 Uint63Axioms, 18 PrimFloat and 10 PrimInt63 primitives. M3's exit criterion is scoped the same way.
2. **VM casts.**
   - 2,961 is now labeled as Flocq's own declarations. The closure adds 790 casts in 263 Stdlib/Corelib declarations, for about 3,751 in about 1,086 declarations.
   - M3 now notes that the cast-free Flocq declarations still depend on Stdlib declarations that contain casts.
   - Casts also come from `ring` and `field`, not only `… = true` checkers.
3. **rocq-lean-import.** The 66,400/11,867 figures are Lean 3 mathlib via `lean --export`, with conversion checking disabled and a 10 s timeout. They are not from lean4export and not a kernel-checked Lean 4 import.
4. **Benchmark.** The 225 s Lean-kernel figure is now tied to the hand-built `Pos.rec` encoding with `maxHeartbeats 0`. A rerun under load took 196 s user. The elaborator-compiled version hits a kernel deterministic timeout. The Rocq numbers reproduced (0.22 s VM, 7.0 s lazy).
5. **`Sort (max u v)`.** The rejection belongs to the elaborator (`MutualInductive.lean:1128`). The kernel accepts the declaration but restricts its recursor to Prop (`inductive.cpp:522-538`).
6. **Large elimination.** "Lean's rule is a superset" is now scoped to Flocq's closure. Rocq allows large elimination for mutual singleton Props and Lean does not (`inductive.cpp:529-531`). None of the closure's inductives is mutual.
7. **SProp.** It is no longer listed as absent. 21 auto-generated `*_sind` eliminators exist and are harmless.
8. **Binary-layer closure.** The `bplus.dpd` evidence had actually been computed for `Bplus_correct`, and had 294 matching lines, not 296. It is replaced by direct counts: `Bplus` 4,622 objects, `Bldexp` 4,638, `Zfast_pow_pos` 17, `mag` 4,153. That puts M1 at about 60% of the closure.
9. **Non-uniform parameters.** Added: `before_witness (n:nat)` recurses at `S n`, and Lean rejects this with `inductiveParamMismatch`. Gilbert's post lists the issue.
10. **Template polymorphism.** The list is completed to 15 inductives (44 objects). Citations are fixed: `sig`/`sigT` are in `Specif.v:29,44`, and `list` is at `Datatypes.v:318`.
11. **Universe-polymorphic objects.** The 37 are now split as 21 CRelationClasses, 15 CMorphisms and 1 `Unconvertible`. They include an inductive and its constructor, so they are "objects", not "constants".
12. **FloatLib.** It has 1,242 files covering IEEE binary/decimal, posits and P3109. 41 is only its Flocq subtree.
13. **CompCert.** `CoInductive` appears in 7 files, not 8; 9 files use any coinductive construct.
14. **CoqInE.** `CoFix` is explicitly unsupported (`src/terms.ml:643`), not merely undocumented.

**Minor (section B):**
- **Header.** It now names `~/FloatSpec/_opam/bin/coqc` and notes that the `coqc` on PATH (Rocq 9.2) was not used.
- **Recursion.**
  - The `fix` census adds `Pff.v:37` (the `fix` tactic) and `Version.v`'s `let fix parse`.
  - "Only guard-checker-only definition" is weakened to "at least one", since no exhaustive scan was done.
  - The well-founded fallback now says that the kernel still unfolds `WellFounded.fix` on closed terms.
- **Coinductive constructors** are described as Prop-typed `def`s, not theorems.
- **Weakened to what the evidence supports:**
  - "11–13 Flocq-owned universe levels" becomes "a handful, about 7 identifiable".
  - The "12 headline theorems" line becomes a 15-declaration sample (12/1/2) and no longer names them.
  - "Prop ≤ Type appears twice" drops "twice". The use itself was re-confirmed from the printed kernel term.
- **Removed claims:**
  - The non-transitivity caveat keeps Carneiro §3.1.1 but drops the link to Lean4Less.
  - The lf-lean Zulip sizes (60k/720k), which could not be verified.
- **ISTA-PLV `#eval` crash** is scoped to its stream test. Its interaction-tree `#eval`s run.
- **Dates:**
  - hol2dk: 2025-01-21 is coq-hol-light 3.0.0; hol2dk's latest release is 2.1.0 (2025-11-20).
  - Mathport: the port was declared complete 2023-07-16; the repo was last pushed 2024-11-21 and is now archived.
- **Mathlib class** is now named `ConditionallyCompleteLinearOrderedField`.
- **"Elaboration only"** is narrowed: classes and instances do reach the kernel as records and constants.
- **Logipedia** is now "unreachable when checked", instead of the earlier HTTP 503.
- **Evidence paths.** Scratchpad (`$S`) paths are replaced by the evidence note in the header. Source file:line citations are kept.
