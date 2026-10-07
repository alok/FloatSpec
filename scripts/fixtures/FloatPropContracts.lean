import FloatSpec.src.Core.Float_prop

namespace FloatPropContracts
open FloatSpec.Core.Defs FloatSpec.Core.Float_prop
open FloatSpec.Core.Raux (bpow mag Rcompare cond_Ropp)
open FloatSpec.Core.Zaux (Zpower cond_Zopp)
open FloatSpec.Core.Digits (Zdigits)

-- Float_prop.v. The section radix is an `Int` with a `ValidRadix` instance (cutover plan E5),
-- which carries `1 < beta`; no lemma takes the invariant a second time. Rocq's
-- `Float beta m e` is `FlocqFloat.mk m e`, `IZR` the integer cast and `Z.abs` is `|·|`.
theorem compare : ∀ (beta : Int) [ValidRadix beta] (e m1 m2 : Int),
    Rcompare (F2R (FlocqFloat.mk m1 e : FlocqFloat beta)) (F2R (FlocqFloat.mk m2 e : FlocqFloat beta)) =
      Ord.compare m1 m2 := Rcompare_F2R
theorem le_inv : ∀ (beta : Int) [ValidRadix beta] (e m1 m2 : Int),
    F2R (FlocqFloat.mk m1 e : FlocqFloat beta) ≤ F2R (FlocqFloat.mk m2 e : FlocqFloat beta) → m1 ≤ m2 :=
  le_F2R
theorem le : ∀ (beta : Int) [ValidRadix beta] (m1 m2 e : Int),
    m1 ≤ m2 → F2R (FlocqFloat.mk m1 e : FlocqFloat beta) ≤ F2R (FlocqFloat.mk m2 e : FlocqFloat beta) :=
  F2R_le
theorem lt_inv : ∀ (beta : Int) [ValidRadix beta] (e m1 m2 : Int),
    F2R (FlocqFloat.mk m1 e : FlocqFloat beta) < F2R (FlocqFloat.mk m2 e : FlocqFloat beta) → m1 < m2 :=
  lt_F2R
theorem lt : ∀ (beta : Int) [ValidRadix beta] (e m1 m2 : Int),
    m1 < m2 → F2R (FlocqFloat.mk m1 e : FlocqFloat beta) < F2R (FlocqFloat.mk m2 e : FlocqFloat beta) :=
  F2R_lt
theorem eq : ∀ (beta : Int) [ValidRadix beta] (e m1 m2 : Int),
    m1 = m2 → F2R (FlocqFloat.mk m1 e : FlocqFloat beta) = F2R (FlocqFloat.mk m2 e : FlocqFloat beta) :=
  F2R_eq
theorem eq_inv : ∀ (beta : Int) [ValidRadix beta] (e m1 m2 : Int),
    F2R (FlocqFloat.mk m1 e : FlocqFloat beta) = F2R (FlocqFloat.mk m2 e : FlocqFloat beta) → m1 = m2 :=
  eq_F2R
theorem abs' : ∀ (beta : Int) [ValidRadix beta] (m e : Int),
    F2R (FlocqFloat.mk |m| e : FlocqFloat beta) = |F2R (FlocqFloat.mk m e : FlocqFloat beta)| := F2R_Zabs
theorem opp : ∀ (beta : Int) [ValidRadix beta] (m e : Int),
    F2R (FlocqFloat.mk (-m) e : FlocqFloat beta) = -F2R (FlocqFloat.mk m e : FlocqFloat beta) := F2R_Zopp
theorem cond_opp : ∀ (beta : Int) [ValidRadix beta] (b : Bool) (m e : Int),
    F2R (FlocqFloat.mk (cond_Zopp b m) e : FlocqFloat beta) =
      cond_Ropp b (F2R (FlocqFloat.mk m e : FlocqFloat beta)) := F2R_cond_Zopp
theorem zero : ∀ (beta : Int) [ValidRadix beta] (e : Int),
    F2R (FlocqFloat.mk 0 e : FlocqFloat beta) = 0 := F2R_0
theorem eq_0 : ∀ (beta : Int) [ValidRadix beta] (m e : Int),
    F2R (FlocqFloat.mk m e : FlocqFloat beta) = 0 → m = 0 := eq_0_F2R
theorem ge_0 : ∀ (beta : Int) [ValidRadix beta] (m e : Int),
    0 ≤ F2R (FlocqFloat.mk m e : FlocqFloat beta) → 0 ≤ m := ge_0_F2R
theorem le_0 : ∀ (beta : Int) [ValidRadix beta] (m e : Int),
    F2R (FlocqFloat.mk m e : FlocqFloat beta) ≤ 0 → m ≤ 0 := le_0_F2R
theorem gt_0 : ∀ (beta : Int) [ValidRadix beta] (m e : Int),
    0 < F2R (FlocqFloat.mk m e : FlocqFloat beta) → 0 < m := gt_0_F2R
theorem lt_0 : ∀ (beta : Int) [ValidRadix beta] (m e : Int),
    F2R (FlocqFloat.mk m e : FlocqFloat beta) < 0 → m < 0 := lt_0_F2R
theorem of_ge_0 : ∀ (beta : Int) [ValidRadix beta] (f : FlocqFloat beta), 0 ≤ f.Fnum → 0 ≤ F2R f :=
  F2R_ge_0
theorem of_le_0 : ∀ (beta : Int) [ValidRadix beta] (f : FlocqFloat beta), f.Fnum ≤ 0 → F2R f ≤ 0 :=
  F2R_le_0
theorem of_gt_0 : ∀ (beta : Int) [ValidRadix beta] (f : FlocqFloat beta), 0 < f.Fnum → 0 < F2R f :=
  F2R_gt_0
theorem of_lt_0 : ∀ (beta : Int) [ValidRadix beta] (f : FlocqFloat beta), f.Fnum < 0 → F2R f < 0 :=
  F2R_lt_0
theorem of_neq_0 : ∀ (beta : Int) [ValidRadix beta] (f : FlocqFloat beta), f.Fnum ≠ 0 → F2R f ≠ 0 :=
  F2R_neq_0
theorem fnum_ge_0 : ∀ (beta : Int) [ValidRadix beta] (f : FlocqFloat beta), 0 ≤ F2R f → 0 ≤ f.Fnum :=
  Fnum_ge_0
theorem fnum_le_0 : ∀ (beta : Int) [ValidRadix beta] (f : FlocqFloat beta), F2R f ≤ 0 → f.Fnum ≤ 0 :=
  Fnum_le_0
theorem of_bpow : ∀ (beta : Int) [ValidRadix beta] (e : Int),
    F2R (FlocqFloat.mk 1 e : FlocqFloat beta) = bpow beta e := F2R_bpow
theorem bpow_le : ∀ (beta : Int) [ValidRadix beta] (m e : Int),
    0 < m → bpow beta e ≤ F2R (FlocqFloat.mk m e : FlocqFloat beta) := bpow_le_F2R
theorem p1_le_bpow : ∀ (beta : Int) [ValidRadix beta] (m e1 e2 : Int), 0 < m →
    F2R (FlocqFloat.mk m e1 : FlocqFloat beta) < bpow beta e2 →
    F2R (FlocqFloat.mk (m + 1) e1 : FlocqFloat beta) ≤ bpow beta e2 := F2R_p1_le_bpow
theorem bpow_le_m1 : ∀ (beta : Int) [ValidRadix beta] (m e1 e2 : Int), 1 < m →
    bpow beta e2 < F2R (FlocqFloat.mk m e1 : FlocqFloat beta) →
    bpow beta e2 ≤ F2R (FlocqFloat.mk (m - 1) e1 : FlocqFloat beta) := bpow_le_F2R_m1
theorem lt_bpow : ∀ (beta : Int) [ValidRadix beta] (f : FlocqFloat beta) (e' : Int),
    |f.Fnum| < Zpower beta (e' - f.Fexp) → |F2R f| < bpow beta e' := F2R_lt_bpow
theorem change_exp : ∀ (beta : Int) [ValidRadix beta] (e' m e : Int), e' ≤ e →
    F2R (FlocqFloat.mk m e : FlocqFloat beta) =
      F2R (FlocqFloat.mk (m * Zpower beta (e - e')) e' : FlocqFloat beta) := F2R_change_exp
theorem prec_normalize : ∀ (beta : Int) [ValidRadix beta] (m e e' p : Int),
    |m| < Zpower beta p → bpow beta (e' - 1) ≤ |F2R (FlocqFloat.mk m e : FlocqFloat beta)| →
    F2R (FlocqFloat.mk m e : FlocqFloat beta) =
      F2R (FlocqFloat.mk (m * Zpower beta (e - e' + p)) (e' - p) : FlocqFloat beta) :=
  F2R_prec_normalize
theorem mag_bounds : ∀ (beta : Int) [ValidRadix beta] (x : ℝ) (m e : Int), 0 < m →
    F2R (FlocqFloat.mk m e : FlocqFloat beta) ≤ x ∧ x < F2R (FlocqFloat.mk (m + 1) e : FlocqFloat beta) →
    mag beta x = mag beta (F2R (FlocqFloat.mk m e : FlocqFloat beta)) := mag_F2R_bounds
theorem mag' : ∀ (beta : Int) [ValidRadix beta] (m e : Int), m ≠ 0 →
    mag beta (F2R (FlocqFloat.mk m e : FlocqFloat beta)) = mag beta (m : ℝ) + e := mag_F2R
theorem digits_mag : ∀ (beta : Int) [ValidRadix beta] (n : Int), n ≠ 0 →
    Zdigits beta n = mag beta (n : ℝ) := Zdigits_mag
theorem mag_digits : ∀ (beta : Int) [ValidRadix beta] (m e : Int), m ≠ 0 →
    mag beta (F2R (FlocqFloat.mk m e : FlocqFloat beta)) = Zdigits beta m + e := mag_F2R_Zdigits
theorem mag_bounds_digits : ∀ (beta : Int) [ValidRadix beta] (x : ℝ) (m e : Int), 0 < m →
    F2R (FlocqFloat.mk m e : FlocqFloat beta) ≤ x ∧ x < F2R (FlocqFloat.mk (m + 1) e : FlocqFloat beta) →
    mag beta x = Zdigits beta m + e := mag_F2R_bounds_Zdigits
theorem distribution_pos : ∀ (beta : Int) [ValidRadix beta] (m1 e1 m2 e2 : Int), 0 < m1 →
    F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) < F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta) ∧
      F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta) < F2R (FlocqFloat.mk (m1 + 1) e1 : FlocqFloat beta) →
    e2 < e1 ∧ e1 + mag beta (m1 : ℝ) = e2 + mag beta (m2 : ℝ) := float_distribution_pos

#print axioms compare
#print axioms prec_normalize
#print axioms distribution_pos

instance : ValidRadix 10 := ⟨by decide⟩

-- 34 · 10⁻¹ = 3.4 changes exponent to 340 · 10⁻²; its magnitude is 1 and it has two digits.
theorem float_prop_contracts_check_1 :
    F2R (FlocqFloat.mk 34 (-1) : FlocqFloat 10) = F2R (FlocqFloat.mk 340 (-2) : FlocqFloat 10) ∧
      Zdigits 10 34 = 2 := by
  refine ⟨?_, by decide⟩
  rw [F2R_change_exp 10 (-2) 34 (-1) (by decide)]
  norm_num [FloatSpec.Core.Zaux.Zpower]

-- `F2R_prec_normalize` needs its lower bound: at 5 · 10⁰ the shifted mantissa 5 · Zpower 10 (-2) is 0.
private theorem prec_normalize_needs_bound : ¬ ∀ m e e' p : Int,
    |m| < Zpower 10 p →
    F2R (FlocqFloat.mk m e : FlocqFloat 10) =
      F2R (FlocqFloat.mk (m * Zpower 10 (e - e' + p)) (e' - p) : FlocqFloat 10) := by
  intro h
  have := h 5 0 3 1 (by decide)
  norm_num [F2R, FloatSpec.Core.Zaux.Zpower] at this

#print axioms prec_normalize_needs_bound

end FloatPropContracts
