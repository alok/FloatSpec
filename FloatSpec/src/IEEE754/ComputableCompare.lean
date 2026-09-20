-- Computable comparison backends for dyadic float payloads, proved equal to
-- the Flocq-faithful real-valued specifications used by `PrimFloat`.
--
-- Motivation.  Flocq states float comparison by first mapping payloads into ℝ
-- (`SF2R`) and then comparing reals.  Transcribed literally under `open
-- Classical`, that makes `SFeqb`/`SFltb`/`SFleb`/`SFcompare` `noncomputable`:
-- `decide (SF2R 2 x = SF2R 2 y)` elaborates through `Classical.propDecidable`,
-- so the resulting `Bool` cannot be evaluated.  Comparison of two binary
-- payloads is nevertheless decidable: `S754_finite s m e` denotes the dyadic
-- rational `(-1)^s * m * 2^e`, and two dyadics are ordered by aligning
-- exponents and comparing integers.
--
-- This module supplies that executable backend and discharges the obligation
-- that matters: each computable function is *proved equivalent* to the
-- real-valued specification it replaces, so the Flocq correspondence is
-- preserved while the interface becomes evaluable.

import FloatSpec.src.IEEE754.PrimFloat

namespace FloatSpec.IEEE754.ComputableCompare

open FloatSpec.Core.Defs (FlocqFloat)
open FloatSpec.Core.Float_prop

/-! ### Dyadic payloads -/

/-- Signed integer mantissa denoted by a sign bit and a magnitude. -/
def signedMantissa (s : Bool) (m : Nat) : Int :=
  if s then -(m : Int) else (m : Int)

/-- Strict order on dyadic payloads `n₁ * beta ^ e₁` vs `n₂ * beta ^ e₂`,
    computed by aligning to the smaller exponent.  Fully computable. -/
def dyadicLt (beta : Int) (n₁ e₁ n₂ e₂ : Int) : Bool :=
  if e₁ ≤ e₂ then n₁ < n₂ * beta ^ (e₂ - e₁).natAbs
  else n₁ * beta ^ (e₁ - e₂).natAbs < n₂

/-- Equality on dyadic payloads, computed by aligning to the smaller
    exponent.  Fully computable. -/
def dyadicEq (beta : Int) (n₁ e₁ n₂ e₂ : Int) : Bool :=
  if e₁ ≤ e₂ then n₁ = n₂ * beta ^ (e₂ - e₁).natAbs
  else n₁ * beta ^ (e₁ - e₂).natAbs = n₂

/-! ### Correspondence with `F2R`

`F2R_change_exp` rewrites a float at any smaller exponent; `lt_F2R_iff` and
`eq_F2R` then compare mantissas at the now-common exponent. -/

section Correspondence

variable {beta : Int} [ValidRadix beta]

/-- Realigning the larger-exponent operand preserves its real value. -/
private theorem val_align (n e e' : Int) (he : e' ≤ e) :
    FloatSpec.Core.Defs.F2R (FlocqFloat.mk n e : FlocqFloat beta)
      = FloatSpec.Core.Defs.F2R
          (FlocqFloat.mk (n * beta ^ (e - e').natAbs) e' : FlocqFloat beta) :=
  F2R_change_exp (beta := beta) (f := FlocqFloat.mk n e) (e' := e')
    ValidRadix.valid he

/-- `dyadicLt` decides the real strict order on dyadic payloads. -/
theorem dyadicLt_iff (n₁ e₁ n₂ e₂ : Int) :
    dyadicLt beta n₁ e₁ n₂ e₂ = true
      ↔ FloatSpec.Core.Defs.F2R (FlocqFloat.mk n₁ e₁ : FlocqFloat beta)
          < FloatSpec.Core.Defs.F2R (FlocqFloat.mk n₂ e₂ : FlocqFloat beta) := by
  unfold dyadicLt
  split
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₂ e₂ e₁ h]
      exact lt_F2R_iff (beta := beta) e₁ _ _ ValidRadix.valid
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₁ e₁ e₂ (not_le.mp h).le]
      exact lt_F2R_iff (beta := beta) e₂ _ _ ValidRadix.valid

/-- `dyadicEq` decides real equality of dyadic payloads. -/
theorem dyadicEq_iff (n₁ e₁ n₂ e₂ : Int) :
    dyadicEq beta n₁ e₁ n₂ e₂ = true
      ↔ FloatSpec.Core.Defs.F2R (FlocqFloat.mk n₁ e₁ : FlocqFloat beta)
          = FloatSpec.Core.Defs.F2R (FlocqFloat.mk n₂ e₂ : FlocqFloat beta) := by
  unfold dyadicEq
  split
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₂ e₂ e₁ h]
      exact ⟨fun hm => congrArg
               (fun m => FloatSpec.Core.Defs.F2R (FlocqFloat.mk m e₁ : FlocqFloat beta)) hm,
             fun hr => eq_F2R (beta := beta) e₁ _ _ hr⟩
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₁ e₁ e₂ (not_le.mp h).le]
      exact ⟨fun hm => congrArg
               (fun m => FloatSpec.Core.Defs.F2R (FlocqFloat.mk m e₂ : FlocqFloat beta)) hm,
             fun hr => eq_F2R (beta := beta) e₂ _ _ hr⟩

end Correspondence

/-! ### Computable `StandardFloat` comparisons

Each function below mirrors the corresponding `FaithfulPrimFloat` definition
arm for arm, replacing only the final real-number test with `dyadicLt` /
`dyadicEq`.  The accompanying theorems prove the replacement exact. -/

section StandardFloatBackend

/-- Dyadic payload `(mantissa, exponent)` denoted by a `StandardFloat`.
    Zero, infinity and NaN all denote `0` under `SF2R`, matching `(0, 0)`. -/
def payload : StandardFloat → Int × Int
  | StandardFloat.S754_finite s m e => (signedMantissa s m, e)
  | _ => (0, 0)

/-- `SF2R` factors through `payload`. -/
theorem SF2R_eq_payload (x : StandardFloat) :
    SF2R 2 x
      = FloatSpec.Core.Defs.F2R
          (FlocqFloat.mk (payload x).1 (payload x).2 : FlocqFloat 2) := by
  cases x <;> simp [SF2R, payload, signedMantissa]

/-- Computable counterpart of `FaithfulPrimFloat.SFltb`. -/
def SFltbC (x y : StandardFloat) : Bool :=
  match x, y with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => sx && !sy
  | StandardFloat.S754_infinity sx, _ => sx
  | _, StandardFloat.S754_infinity sy => !sy
  | x, y => dyadicLt 2 (payload x).1 (payload x).2 (payload y).1 (payload y).2

/-- Computable counterpart of `FaithfulPrimFloat.SFeqb`. -/
def SFeqbC (x y : StandardFloat) : Bool :=
  match x, y with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => sx == sy
  | StandardFloat.S754_infinity _, _ => false
  | _, StandardFloat.S754_infinity _ => false
  | x, y => dyadicEq 2 (payload x).1 (payload x).2 (payload y).1 (payload y).2

/-- Computable counterpart of `FaithfulPrimFloat.SFleb`. -/
def SFlebC (x y : StandardFloat) : Bool :=
  SFltbC x y || SFeqbC x y

/-- Computable counterpart of `FaithfulPrimFloat.SFcompare`. -/
def SFcompareC (x y : StandardFloat) : Option Ordering :=
  match x, y with
  | StandardFloat.S754_nan, _ => none
  | _, StandardFloat.S754_nan => none
  | x, y =>
      if SFltbC x y then some Ordering.lt
      else if SFltbC y x then some Ordering.gt
      else some Ordering.eq

/-- The executable strict order agrees with the Flocq specification. -/
@[simp] theorem SFltbC_eq (x y : StandardFloat) :
    SFltbC x y = FaithfulPrimFloat.SFltb x y := by
  cases x <;> cases y <;>
    simp only [SFltbC, FaithfulPrimFloat.SFltb] <;>
    rw [Bool.eq_iff_iff, dyadicLt_iff, decide_eq_true_eq,
        SF2R_eq_payload, SF2R_eq_payload]

/-- The executable equality test agrees with the Flocq specification. -/
@[simp] theorem SFeqbC_eq (x y : StandardFloat) :
    SFeqbC x y = FaithfulPrimFloat.SFeqb x y := by
  cases x <;> cases y <;>
    simp only [SFeqbC, FaithfulPrimFloat.SFeqb] <;>
    rw [Bool.eq_iff_iff, dyadicEq_iff, decide_eq_true_eq,
        SF2R_eq_payload, SF2R_eq_payload]

/-- The executable non-strict order agrees with the Flocq specification. -/
@[simp] theorem SFlebC_eq (x y : StandardFloat) :
    SFlebC x y = FaithfulPrimFloat.SFleb x y := by
  simp [SFlebC, FaithfulPrimFloat.SFleb]

/-- The executable three-way comparison agrees with the Flocq specification. -/
@[simp] theorem SFcompareC_eq (x y : StandardFloat) :
    SFcompareC x y = FaithfulPrimFloat.SFcompare x y := by
  cases x <;> cases y <;> simp [SFcompareC, FaithfulPrimFloat.SFcompare]

end StandardFloatBackend

end FloatSpec.IEEE754.ComputableCompare
