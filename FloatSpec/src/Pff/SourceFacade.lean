import FloatSpec.src.Pff.Pff
import FloatSpec.Linter.CoqSourceLinter

/-!
# Source-faithful Pff boundary

The legacy `Pff.v` development predates FLoCq's radix-indexed Core float.  Its
exported `float` record is therefore independent of a radix, and operations
such as `FtoR`, `digit`, and `Fnormalize` take an unrestricted integer radix.

The main translated Pff implementation is integrated with FloatSpec's
radix-indexed Core representation.  This module provides the exact external
Pff data model and explicit bridges at the boundary, instead of silently
adding `[ValidRadix beta]` to source declarations that do not export it.
-/

namespace FloatSpec.Pff.Source

set_option linter.coqSource true

/-- Coq `Pff.float`: an unindexed pair of integer mantissa and exponent. -/
@[flocq_source "src/Pff/Pff.v" 1134 "float"]
structure float where
  Fnum : Int
  Fexp : Int
deriving DecidableEq, Repr

/-- Source zero retains the requested exponent in its raw representation. -/
@[flocq_source "src/Pff/Pff.v" 1151 "Fzero"]
def Fzero (exponent : Int) : float := ⟨0, exponent⟩

/-- Source zero predicate tests the mantissa, not the chosen exponent. -/
@[flocq_source "src/Pff/Pff.v" 1153 "is_Fzero"]
def is_Fzero (x : float) : Prop := x.Fnum = 0

/-- Forget the Core radix index. -/
@[flocq_local "Forget the Lean Core radix index at the Pff boundary"]
def float.ofCore {beta : Int} [ValidRadix beta]
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : float :=
  ⟨x.Fnum, x.Fexp⟩

/-- Refine a source Pff float into the Core carrier at a valid radix. -/
@[flocq_local "Refine the unindexed Pff carrier into Lean Core"]
def float.toCore (beta : Int) [ValidRadix beta]
    (x : float) : FloatSpec.Core.Defs.FlocqFloat beta :=
  ⟨x.Fnum, x.Fexp⟩

@[simp] theorem float.ofCore_toCore (beta : Int) [ValidRadix beta]
    (x : float) : float.ofCore (x.toCore beta) = x := by
  cases x
  rfl

@[simp] theorem float.toCore_ofCore {beta : Int} [ValidRadix beta]
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    (float.ofCore x).toCore beta = x := by
  cases x
  rfl

/-- Coq `Pff.FtoR`, total at every integer radix exported by the source. -/
@[flocq_source "src/Pff/Pff.v" 1158 "FtoR"]
noncomputable def FtoR (radix : Int) (x : float) : Real :=
  (x.Fnum : Real) * (radix : Real) ^ x.Fexp

/-- Every source zero represents real zero, including at unrestricted radices. -/
@[flocq_source "src/Pff/Pff.v" 1162 "FzeroisReallyZero"]
theorem FzeroisReallyZero (radix exponent : Int) : FtoR radix (Fzero exponent) = 0 := by
  simp [FtoR, Fzero]

/-- A zero mantissa represents zero without any radix restriction. -/
@[flocq_source "src/Pff/Pff.v" 1166 "is_Fzero_rep1"]
theorem is_Fzero_rep1 (radix : Int) (x : float) (hx : is_Fzero x) :
    FtoR radix x = 0 := by
  simp [FtoR, show x.Fnum = 0 from hx]

/-- The source converse retains its explicit valid-radix premise. -/
@[flocq_source "src/Pff/Pff.v" 1179 "is_Fzero_rep2"]
theorem is_Fzero_rep2 (radix : Int) (hradix : 1 < radix) (x : float)
    (hx : FtoR radix x = 0) : is_Fzero x := by
  have hradix_pos : (0 : Real) < radix := by exact_mod_cast (by omega : 0 < radix)
  have hpower : (radix : Real) ^ x.Fexp ≠ 0 := ne_of_gt (zpow_pos hradix_pos _)
  have hmantissa : (x.Fnum : Real) = 0 := (mul_eq_zero.mp hx).resolve_right hpower
  exact_mod_cast hmantissa

/-- At a valid matching radix, the source observer agrees definitionally with
FloatSpec's indexed Core observer. -/
@[simp] theorem FtoR_toCore (beta : Int) [ValidRadix beta] (x : float) :
    FtoR beta x = _root_.F2R (x.toCore beta) := by
  rfl

@[flocq_source "src/Pff/Pff.v" 1385 "Fle"]
def Fle (radix : Int) (x y : float) : Prop :=
  FtoR radix x ≤ FtoR radix y

@[flocq_source "src/Pff/Pff.v" 5227 "UniqueP"]
def UniqueP (radix : Int) (P : Real → float → Prop) : Prop :=
  ∀ r p q, P r p → P r q → FtoR radix p = FtoR radix q

@[flocq_source "src/Pff/Pff.v" 4529 "MonotoneP"]
def MonotoneP (radix : Int) (P : Real → float → Prop) : Prop :=
  ∀ p q p' q', p < q → P p p' → P q q' →
    FtoR radix p' ≤ FtoR radix q'

@[flocq_source "src/Pff/Pff.v" 4695 "MinExList"]
theorem MinExList (radix : Int) (r : Real) (L : List float) :
    (∀ f ∈ L, r < FtoR radix f) ∨
    ∃ min ∈ L, FtoR radix min ≤ r ∧
      ∀ f ∈ L, FtoR radix f ≤ r → FtoR radix f ≤ FtoR radix min := by
  induction L with
  | nil => left; simp
  | cons a L ih =>
      by_cases ha : FtoR radix a ≤ r
      · right
        rcases ih with hall | ⟨m, hm, hmr, hmin⟩
        · exact ⟨a, by simp, ha, fun f hf hfr => by
            rcases List.mem_cons.mp hf with rfl | hf
            · exact le_rfl
            · exact absurd hfr (not_le.mpr (hall f hf))⟩
        · by_cases ham : FtoR radix a ≤ FtoR radix m
          · exact ⟨m, by simp [hm], hmr, fun f hf hfr => by
              rcases List.mem_cons.mp hf with rfl | hf
              · exact ham
              · exact hmin f hf hfr⟩
          · exact ⟨a, by simp, ha, fun f hf hfr => by
              rcases List.mem_cons.mp hf with rfl | hf
              · exact le_rfl
              · exact (hmin f hf hfr).trans (le_of_not_ge ham)⟩
      · push Not at ha
        rcases ih with hall | ⟨m, hm, hmr, hmin⟩
        · left
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact ha
          · exact hall f hf
        · right
          exact ⟨m, by simp [hm], hmr, fun f hf hfr => by
            rcases List.mem_cons.mp hf with rfl | hf
            · exact absurd hfr (not_le.mpr ha)
            · exact hmin f hf hfr⟩

@[flocq_source "src/Pff/Pff.v" 1504 "Fopp"]
def Fopp (x : float) : float :=
  ⟨-x.Fnum, x.Fexp⟩

/-- Source negation preserves the real interpretation at every integer radix. -/
@[flocq_source "src/Pff/Pff.v" 1506 "Fopp_correct"]
theorem Fopp_correct (radix : Int) (x : float) :
    FtoR radix (Fopp x) = -FtoR radix x := by
  simp [FtoR, Fopp]

/-- Two source negations restore the complete raw record. -/
@[flocq_source "src/Pff/Pff.v" 1512 "Fopp_Fopp"]
theorem Fopp_Fopp (x : float) : Fopp (Fopp x) = x := by
  cases x
  simp [Fopp]

@[flocq_source "src/Pff/Pff.v" 1524 "Fabs"]
def Fabs (x : float) : float :=
  ⟨x.Fnum.natAbs, x.Fexp⟩

/-- The source absolute-value observer law retains positivity, including radix one. -/
@[flocq_source "src/Pff/Pff.v" 1567 "Fabs_correct"]
theorem Fabs_correct (radix : Int) (hradix : 0 < radix) (x : float) :
    FtoR radix (Fabs x) = |FtoR radix x| := by
  have hradix_pos : (0 : Real) < radix := by exact_mod_cast hradix
  simp [FtoR, Fabs, abs_mul, abs_of_pos (zpow_pos hradix_pos x.Fexp)]

/-- Source absolute value cannot turn a nonzero mantissa into zero. -/
@[flocq_source "src/Pff/Pff.v" 1593 "Fabs_Fzero"]
theorem Fabs_Fzero (x : float) (hx : ¬ is_Fzero x) : ¬ is_Fzero (Fabs x) := by
  simpa [is_Fzero, Fabs] using hx

/-- Coq `Pff.boundNat`, including its total behavior at every integer radix. -/
-- Source ID: Pff/Pff.v:boundNat:150939
@[flocq_source "src/Pff/Pff.v" 4322 "boundNat"]
def boundNat (radix : Int) (n : Nat) : float :=
  ⟨1, _root_.digit radix n⟩

/-- Coq `Pff.boundR`; `up` is the strict ceiling `floor x + 1`. -/
-- Source ID: Pff/Pff.v:boundR:151409
@[flocq_source "src/Pff/Pff.v" 4336 "boundR"]
noncomputable def boundR (radix : Int) (r : Real) : float :=
  boundNat radix (Int.natAbs (Int.floor |r| + 1))

/-- Coq `Pff.boundRrOpp`. -/
-- Source ID: Pff/Pff.v:boundRrOpp:152106
@[flocq_source "src/Pff/Pff.v" 4355 "boundRrOpp"]
theorem boundRrOpp (radix : Int) (r : Real) :
    boundR radix r = boundR radix (-r) := by
  simp [boundR, abs_neg]

@[flocq_source "src/Pff/Pff.v" 1483 "Fplus"]
def Fplus (radix : Int) (x y : float) : float :=
  let commonExp := min x.Fexp y.Fexp
  ⟨x.Fnum * radix ^ Int.natAbs (x.Fexp - commonExp) +
      y.Fnum * radix ^ Int.natAbs (y.Fexp - commonExp),
    commonExp⟩

@[flocq_source "src/Pff/Pff.v" 1605 "Fminus"]
def Fminus (radix : Int) (x y : float) : float :=
  Fplus radix x (Fopp y)

/-- Source multiplication uses only the unindexed integer fields. -/
@[flocq_source "src/Pff/Pff.v" 1628 "Fmult"]
def Fmult (x y : float) : float := ⟨x.Fnum * y.Fnum, x.Fexp + y.Fexp⟩

/-- The source multiplication law needs a positive radix, including radix one. -/
@[flocq_source "src/Pff/Pff.v" 1630 "Fmult_correct"]
theorem Fmult_correct (radix : Int) (hradix : 0 < radix) (x y : float) :
    FtoR radix (Fmult x y) = FtoR radix x * FtoR radix y := by
  have hradix_pos : (0 : Real) < radix := by exact_mod_cast hradix
  simp only [FtoR, Fmult, Int.cast_mul, zpow_add₀ (ne_of_gt hradix_pos)]
  ring

/-- Source-shaped counterpart of Coq's `positive × N` bound record. -/
@[flocq_source "src/Pff/Pff.v" 1664 "Fbound"]
structure Fbound where
  vNum : Nat
  dExp : Nat
  vNum_pos : 0 < vNum

/-- Refine the source carrier into the arithmetic-friendly integrated bound. -/
@[flocq_local "Convert source positive/natural bounds into Lean integer refinements"]
def Fbound.toIntegrated (b : Fbound) : _root_.Fbound :=
  { vNum := b.vNum
    dExp := b.dExp
    vNum_pos := by exact_mod_cast b.vNum_pos
    dExp_nonneg := by omega }

/-- Forget the integer refinement representation used by the integrated layer. -/
@[flocq_local "Recover source positive/natural bounds from Lean integer refinements"]
def Fbound.ofIntegrated (b : _root_.Fbound) : Fbound :=
  { vNum := b.vNum.natAbs
    dExp := b.dExp.natAbs
    vNum_pos := by
      rw [Int.natAbs_pos]
      exact ne_of_gt b.vNum_pos
    }

@[simp] theorem Fbound.ofIntegrated_toIntegrated (b : Fbound) :
    Fbound.ofIntegrated b.toIntegrated = b := by
  cases b with
  | mk vNum dExp vNum_pos =>
      simp [Fbound.toIntegrated, Fbound.ofIntegrated]

@[simp] theorem Fbound.toIntegrated_ofIntegrated (b : _root_.Fbound) :
    (Fbound.ofIntegrated b).toIntegrated = b := by
  cases b with
  | mk dExp vNum dExp_nonneg vNum_pos =>
      simp [Fbound.ofIntegrated, Fbound.toIntegrated,
        Int.natAbs_of_nonneg dExp_nonneg,
        Int.natAbs_of_nonneg (le_of_lt vNum_pos)]

@[flocq_source "src/Pff/Pff.v" 1666 "Fbounded"]
def Fbounded (b : Fbound) (x : float) : Prop :=
  |x.Fnum| < (b.vNum : Int) ∧ -(b.dExp : Int) ≤ x.Fexp

@[flocq_source "src/Pff/Pff.v" 2123 "Fnormal"]
def Fnormal (radix : Int) (b : Fbound) (x : float) : Prop :=
  Fbounded b x ∧ (b.vNum : Int) ≤ |radix * x.Fnum|

@[flocq_source "src/Pff/Pff.v" 2184 "Fsubnormal"]
def Fsubnormal (radix : Int) (b : Fbound) (x : float) : Prop :=
  Fbounded b x ∧ x.Fexp = -(b.dExp : Int) ∧
    |radix * x.Fnum| < (b.vNum : Int)

@[flocq_source "src/Pff/Pff.v" 2234 "Fcanonic"]
def Fcanonic (radix : Int) (b : Fbound) (x : float) : Prop :=
  Fnormal radix b x ∨ Fsubnormal radix b x

@[simp] theorem Fbounded_toCore (beta : Int) [ValidRadix beta]
    (b : Fbound) (x : float) :
    Fbounded b x ↔ _root_.Fbounded b.toIntegrated (x.toCore beta) := by
  rfl

@[simp] theorem Fnormal_toCore (beta : Int) [ValidRadix beta]
    (radix : Int) (b : Fbound) (x : float) :
    Fnormal radix b x ↔
      _root_.Fnormal radix b.toIntegrated (x.toCore beta) := by
  rfl

@[simp] theorem Fsubnormal_toCore (beta : Int) [ValidRadix beta]
    (radix : Int) (b : Fbound) (x : float) :
    Fsubnormal radix b x ↔
      _root_.Fsubnormal radix b.toIntegrated (x.toCore beta) := by
  rfl

@[simp] theorem Fcanonic_toCore (beta : Int) [ValidRadix beta]
    (radix : Int) (b : Fbound) (x : float) :
    Fcanonic radix b x ↔
      _root_.Fcanonic radix b.toIntegrated (x.toCore beta) := by
  rfl

private def digitAuxFuel (radix value : Int) : Int → Nat → Nat
  | _, 0 => 0
  | power, fuel + 1 =>
      if power > value then 0
      else Nat.succ (digitAuxFuel radix value (radix * power) fuel)

/-- Coq `Pff.digit`, retaining the source structural recursion on the entire
integer-radix domain.  The fuel is the constructor depth of `xO |q|`. -/
@[flocq_source "src/Pff/Pff.v" 564 "digit"]
def digit (radix q : Int) : Nat :=
  if q = 0 then 0
  else digitAuxFuel radix q.natAbs 1 (Nat.log2 q.natAbs + 1)

@[flocq_source "src/Pff/Pff.v" 1265 "Fdigit"]
def Fdigit (radix : Int) (x : float) : Nat :=
  digit radix x.Fnum

@[flocq_source "src/Pff/Pff.v" 1267 "Fshift"]
def Fshift (radix : Int) (amount : Nat) (x : float) : float :=
  ⟨x.Fnum * radix ^ amount, x.Fexp - (amount : Int)⟩

/-- Coq `Pff.Fnormalize`, including its observable behavior outside the
section's non-exported `1 < radix` hypothesis. -/
@[flocq_source "src/Pff/Pff.v" 2622 "Fnormalize"]
def Fnormalize (radix : Int) (b : Fbound) (precision : Nat)
    (x : float) : float :=
  if x.Fnum = 0 then
    ⟨0, -(b.dExp : Int)⟩
  else
    Fshift radix
      (min (precision - Fdigit radix x)
        (Int.natAbs ((b.dExp : Int) + x.Fexp)))
      x

/-- Coq `Pff.Fulp`, observed using the same explicit radix that normalization
uses rather than an independent type index. -/
@[flocq_source "src/Pff/Pff.v" 6268 "Fulp"]
noncomputable def Fulp (b : Fbound) (radix : Int) (precision : Nat)
    (x : float) : Real :=
  (radix : Real) ^ (Fnormalize radix b precision x).Fexp

/-- Coq `Pff.nNormMin`, retaining the source `Nat.pred` at precision zero. -/
@[flocq_source "src/Pff/Pff.v" 2460 "nNormMin"]
def nNormMin (radix : Int) (precision : Nat) : Int :=
  Zpower_nat radix (Nat.pred precision)

/-- Coq `Pff.firstNormalPos`. -/
@[flocq_source "src/Pff/Pff.v" 2481 "firstNormalPos"]
def firstNormalPos (radix : Int) (b : Fbound)
    (precision : Nat) : float :=
  ⟨nNormMin radix precision, -(b.dExp : Int)⟩

/-- Flocq's integer-mantissa parity predicate. -/
@[flocq_source "src/Pff/Pff.v" 5043 "Feven"]
def Feven (p : float) : Prop := Even p.Fnum

/-- Flocq's integer-mantissa oddness predicate. -/
@[flocq_source "src/Pff/Pff.v" 5045 "Fodd"]
def Fodd (p : float) : Prop := Odd p.Fnum

/-- Source-shaped successor, using only the explicit integer radix. -/
@[flocq_source "src/Pff/Pff.v" 2976 "FSucc"]
def FSucc (b : Fbound) (radix : Int) (precision : Nat)
    (x : float) : float :=
  if x.Fnum = (b.vNum : Int) - 1 then
    ⟨nNormMin radix precision, x.Fexp + 1⟩
  else if x.Fnum = -nNormMin radix precision then
    if x.Fexp = -(b.dExp : Int) then
      ⟨x.Fnum + 1, x.Fexp⟩
    else
      ⟨-((b.vNum : Int) - 1), x.Fexp - 1⟩
  else
    ⟨x.Fnum + 1, x.Fexp⟩

/-- Source-shaped predecessor, using only the explicit integer radix. -/
@[flocq_source "src/Pff/Pff.v" 3904 "FPred"]
def FPred (b : Fbound) (radix : Int) (precision : Nat)
    (x : float) : float :=
  if x.Fnum = -((b.vNum : Int) - 1) then
    ⟨-nNormMin radix precision, x.Fexp + 1⟩
  else if x.Fnum = nNormMin radix precision then
    if x.Fexp = -(b.dExp : Int) then
      ⟨x.Fnum - 1, x.Fexp⟩
    else
      ⟨(b.vNum : Int) - 1, x.Fexp - 1⟩
  else
    ⟨x.Fnum - 1, x.Fexp⟩

/-- Flocq normalizes with this same explicit radix before taking a successor. -/
@[flocq_source "src/Pff/Pff.v" 3819 "FNSucc"]
def FNSucc (b : Fbound) (radix : Int) (precision : Nat)
    (x : float) : float :=
  FSucc b radix precision (Fnormalize radix b precision x)

/-- Flocq normalizes with this same explicit radix before taking a predecessor. -/
@[flocq_source "src/Pff/Pff.v" 4110 "FNPred"]
def FNPred (b : Fbound) (radix : Int) (precision : Nat)
    (x : float) : float :=
  FPred b radix precision (Fnormalize radix b precision x)

/-- Normalized-even parity uses the source's explicit radix. -/
@[flocq_source "src/Pff/Pff.v" 5131 "FNeven"]
def FNeven (b : Fbound) (radix : Int) (precision : Nat)
    (x : float) : Prop :=
  Feven (Fnormalize radix b precision x)

/-- Normalized-odd parity uses the source's explicit radix. -/
@[flocq_source "src/Pff/Pff.v" 5129 "FNodd"]
def FNodd (b : Fbound) (radix : Int) (precision : Nat)
    (x : float) : Prop :=
  Fodd (Fnormalize radix b precision x)

/-- The unnormalized successor commutes with the carrier conversion, at every
explicit operational radix. No equality with the Core type index is needed. -/
theorem FSucc_toCore (beta : Int) [ValidRadix beta] (b : Fbound)
    (radix : Int) (precision : Nat) (x : float) :
    float.ofCore (_root_.FSucc b.toIntegrated radix precision (x.toCore beta)) =
      FSucc b radix precision x := by
  by_cases hmax : x.Fnum = (b.vNum : Int) - 1 <;>
    by_cases hmin : x.Fnum = -(radix ^ (precision - 1)) <;>
    by_cases hexp : x.Fexp = -(b.dExp : Int) <;>
    simp [float.ofCore, float.toCore, Fbound.toIntegrated,
      _root_.FSucc, FSucc, pPred, _root_.nNormMin, nNormMin, Zpower_nat,
      Nat.pred_eq_sub_one, hmax, hmin, hexp]
  all_goals simp_all

/-- The unnormalized predecessor also commutes with the carrier conversion,
independently of the Core type index. -/
theorem FPred_toCore (beta : Int) [ValidRadix beta] (b : Fbound)
    (radix : Int) (precision : Nat) (x : float) :
    float.ofCore (_root_.FPred b.toIntegrated radix precision (x.toCore beta)) =
      FPred b radix precision x := by
  by_cases hmax : x.Fnum = -((b.vNum : Int) - 1) <;>
    by_cases hmin : x.Fnum = radix ^ (precision - 1) <;>
    by_cases hexp : x.Fexp = -(b.dExp : Int) <;>
    simp [float.ofCore, float.toCore, Fbound.toIntegrated,
      _root_.FPred, FPred, pPred, _root_.nNormMin, nNormMin, Zpower_nat,
      Nat.pred_eq_sub_one, hmax, hmin, hexp]
  all_goals simp_all

/-- Rocq Stdlib's natural logarithm is zero on nonpositive inputs.

This differs from Lean's {name}`Real.log`, which is extended using absolute
value. Pff's total source-facing definitions must retain the Rocq convention,
even outside the positive-radix hypotheses of their correctness theorems. -/
@[flocq_local "Rocq Stdlib Rpower.ln extension used by Pff; not a Flocq-owned declaration"]
noncomputable def rocqLn (x : Real) : Real :=
  if 0 < x then Real.log x else 0

/-- Coq `Pff.RND_Min_Pos`.

The source declaration has one explicit radix and a natural precision.  In
particular, the threshold is observed with that same radix; there is no
independent type-level `beta` that could select a different branch. -/
@[flocq_source "src/Pff/Pff.v" 27157 "RND_Min_Pos"]
noncomputable def RND_Min_Pos (b : Fbound) (radix : Int)
    (precision : Nat) (r : Real) : float :=
  let firstNormPosValue := FtoR radix (firstNormalPos radix b precision)
  if firstNormPosValue ≤ r then
    let e : Int :=
      IRNDD (rocqLn r / rocqLn (radix : Real) +
        (-(precision : Int) + 1 : Int))
    ⟨IRNDD (r * (radix : Real) ^ (-e)), e⟩
  else
    ⟨IRNDD (r * (radix : Real) ^ (b.dExp : Int)), -(b.dExp : Int)⟩


/-- Source upper rounding of a positive input; exact inputs retain the lower
record, while inexact inputs use its raw successor. -/
@[flocq_source "src/Pff/Pff.v" 27523 "RND_Max_Pos"]
noncomputable def RND_Max_Pos (b : Fbound) (radix : Int)
    (precision : Nat) (r : Real) : float :=
  let lower := RND_Min_Pos b radix precision r
  if r = FtoR radix lower then lower
  else FSucc b radix precision lower

/-- Source signed downward rounding, with the same explicit radix throughout. -/
@[flocq_source "src/Pff/Pff.v" 27588 "RND_Min"]
noncomputable def RND_Min (b : Fbound) (radix : Int)
    (precision : Nat) (r : Real) : float :=
  if 0 ≤ r then RND_Min_Pos b radix precision r
  else Fopp (RND_Max_Pos b radix precision (-r))

/-- Source signed upward rounding, with the same explicit radix throughout. -/
@[flocq_source "src/Pff/Pff.v" 27611 "RND_Max"]
noncomputable def RND_Max (b : Fbound) (radix : Int)
    (precision : Nat) (r : Real) : float :=
  if 0 ≤ r then RND_Max_Pos b radix precision r
  else Fopp (RND_Min_Pos b radix precision (-r))

/-- Source nearest-even selector. At an equal-distance tie it tests the
lower result's integer mantissa, not a different indexed normalization. -/
@[flocq_source "src/Pff/Pff.v" 27641 "RND_EvenClosest"]
noncomputable def RND_EvenClosest (b : Fbound) (radix : Int)
    (precision : Nat) (r : Real) : float :=
  let upper := RND_Max b radix precision r
  let lower := RND_Min b radix precision r
  if |FtoR radix upper - r| ≤ |FtoR radix lower - r| then
    if |FtoR radix upper - r| < |FtoR radix lower - r| then upper
    else if Odd lower.Fnum then upper else lower
  else lower

-- These older indexed entry points are compatibility APIs, not the total
-- unindexed source exports above. Their legacy radix argument is ignored.
attribute [flocq_local "Indexed normalized-even compatibility predicate; use FloatSpec.Pff.Source.FNeven for the explicit-radix source export"] _root_.FNeven
attribute [flocq_local "Indexed normalized-odd compatibility predicate; use FloatSpec.Pff.Source.FNodd for the explicit-radix source export"] _root_.FNodd
attribute [flocq_local "Indexed normalized-successor compatibility adapter; use FloatSpec.Pff.Source.FNSucc for the explicit-radix source export"] _root_.FNSucc
attribute [flocq_local "Indexed normalized-predecessor compatibility adapter; use FloatSpec.Pff.Source.FNPred for the explicit-radix source export"] _root_.FNPred

-- This distinct legacy signature also has integer precision and an independent
-- Core radix. Its positive/matching-radix proof domain is not a total-source claim.
attribute [flocq_local "Legacy indexed rounding implementation; the total source interface is FloatSpec.Pff.Source.RND_Min_Pos"] _root_.RND_Min_Pos
attribute [flocq_local "Legacy indexed rounding adapter; use the single-radix source RND_Max_Pos"] _root_.RND_Max_Pos
attribute [flocq_local "Legacy indexed signed downward-rounding adapter; use FloatSpec.Pff.Source.RND_Min"] _root_.RND_Min
attribute [flocq_local "Legacy indexed signed upward-rounding adapter; use FloatSpec.Pff.Source.RND_Max"] _root_.RND_Max
attribute [flocq_local "Legacy indexed nearest-even adapter; use FloatSpec.Pff.Source.RND_EvenClosest"] _root_.RND_EvenClosest

end FloatSpec.Pff.Source
