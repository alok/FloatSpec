import FloatSpec.src.Core.Raux

namespace RauxPowContracts
open FloatSpec.Core.Raux

-- Raux.v:1331-1582. The radix is an `Int` with its invariant `1 < beta` as a premise
-- (cutover plan E5) where Rocq bundles `2 <= r` in the `radix` record. Rocq's `powerRZ` is
-- Lean's `zpow`, so `bpow` is that power by definition, as `bpow_powerRZ` states in Rocq.
example (beta e : Int) : bpow beta e = (beta : ℝ) ^ e := rfl

theorem radix_positive : ∀ beta : Int, 1 < beta → 0 < (beta : ℝ) := radix_pos
theorem izr_zpower_pos : ∀ (n : Int) (m : FloatSpec.Core.Zaux.Positive),
    ((FloatSpec.Core.Zaux.Zpower_pos n m : Int) : ℝ) = (n : ℝ) ^ (FloatSpec.Core.Zaux.Zpos m) :=
  IZR_Zpower_pos
theorem bpow_is_powerRZ : ∀ beta e : Int, 1 < beta → bpow beta e = (beta : ℝ) ^ e := bpow_powerRZ
theorem bpow_nonneg : ∀ beta e : Int, 1 < beta → 0 ≤ bpow beta e := bpow_ge_0
theorem bpow_positive : ∀ beta e : Int, 1 < beta → 0 < bpow beta e := bpow_gt_0
theorem bpow_add : ∀ beta e1 e2 : Int, 1 < beta →
    bpow beta (e1 + e2) = bpow beta e1 * bpow beta e2 := bpow_plus
theorem bpow_one : ∀ beta : Int, 1 < beta → bpow beta 1 = (beta : ℝ) := bpow_1
theorem bpow_succ : ∀ beta e : Int, 1 < beta → bpow beta (e + 1) = (beta : ℝ) * bpow beta e :=
  bpow_plus_1
theorem bpow_neg : ∀ beta e : Int, 1 < beta → bpow beta (-e) = (bpow beta e)⁻¹ := bpow_opp
theorem izr_zpower_nat : ∀ (r : FloatSpec.Core.Zaux.Radix) (e : Nat),
    ((r.val ^ e : Int) : ℝ) = bpow r.val (Int.ofNat e) := IZR_Zpower_nat
theorem izr_zpower : ∀ (r : FloatSpec.Core.Zaux.Radix) (e : Int), 0 ≤ e →
    ((FloatSpec.Core.Zaux.Zpower r.val e : Int) : ℝ) = bpow r.val e := IZR_Zpower
theorem bpow_strict : ∀ beta e1 e2 : Int, 1 < beta → e1 < e2 → bpow beta e1 < bpow beta e2 :=
  bpow_lt
theorem bpow_strict_inv : ∀ beta e1 e2 : Int, 1 < beta → bpow beta e1 < bpow beta e2 → e1 < e2 :=
  lt_bpow
theorem bpow_mono : ∀ beta e1 e2 : Int, 1 < beta → e1 ≤ e2 → bpow beta e1 ≤ bpow beta e2 :=
  bpow_le
theorem bpow_mono_inv : ∀ beta e1 e2 : Int, 1 < beta → bpow beta e1 ≤ bpow beta e2 → e1 ≤ e2 :=
  le_bpow
theorem bpow_injective : ∀ beta e1 e2 : Int, 1 < beta → bpow beta e1 = bpow beta e2 → e1 = e2 :=
  bpow_inj
theorem bpow_exponential : ∀ beta e : Int, 1 < beta →
    bpow beta e = Real.exp ((e : ℝ) * Real.log (beta : ℝ)) := bpow_exp
theorem bpow_sqrt : ∀ beta e : Int, 1 < beta → Real.sqrt (bpow beta (2 * e)) = bpow beta e :=
  sqrt_bpow
theorem bpow_sqrt_ge : ∀ beta e : Int, 1 < beta → bpow beta (e / 2) ≤ Real.sqrt (bpow beta e) :=
  sqrt_bpow_ge

#print axioms bpow_mono
#print axioms bpow_exponential

-- Concrete values: negative exponents are reciprocals, not truncations.
example : bpow 2 (-3) = 8⁻¹ ∧ bpow 10 2 = 100 := by norm_num [bpow]

-- Unbundled, the radix invariant is needed: at radix 0, 0⁰ = 1 exceeds 0¹ = 0.
private theorem bpow_le_needs_radix :
    ¬ ∀ beta e1 e2 : Int, e1 ≤ e2 → bpow beta e1 ≤ bpow beta e2 := by
  intro h
  have := h 0 0 1 (by norm_num)
  norm_num [bpow] at this

#print axioms bpow_le_needs_radix

end RauxPowContracts
