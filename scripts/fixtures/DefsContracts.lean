import FloatSpec.src.Core.Defs

namespace DefsContracts
open FloatSpec.Core.Defs FloatSpec.Core.Raux

-- Defs.v. Rocq's `float beta` with constructor `Float` is Lean's `FlocqFloat beta` with `mk`
-- (cutover plan E9: a `Float` constructor would shadow Lean's `Float`); the radix is an `Int`
-- with a `ValidRadix` instance (E5).
theorem fnum_field (beta : Int) [ValidRadix beta] (m e : Int) : (FlocqFloat.mk m e : FlocqFloat beta).Fnum = m :=
  rfl
theorem fexp_field (beta : Int) [ValidRadix beta] (m e : Int) : (FlocqFloat.mk m e : FlocqFloat beta).Fexp = e :=
  rfl

-- Every definition, pinned to the source body (bpow is reducible, so F2R reads as the source).
theorem f2r_body (beta : Int) [ValidRadix beta] (f : FlocqFloat beta) :
    F2R f = (f.Fnum : ℝ) * bpow beta f.Fexp := rfl
theorem total_body (P : ℝ → ℝ → Prop) : round_pred_total P = ∀ x, ∃ f, P x f := rfl
theorem monotone_body (P : ℝ → ℝ → Prop) :
    round_pred_monotone P = ∀ x y f g, P x f → P y g → x ≤ y → f ≤ g := rfl
theorem pred_body (P : ℝ → ℝ → Prop) : round_pred P = (round_pred_total P ∧ round_pred_monotone P) := rfl
theorem dn_body (F : ℝ → Prop) (x f : ℝ) :
    Rnd_DN_pt F x f = (F f ∧ f ≤ x ∧ ∀ g, F g → g ≤ x → g ≤ f) := rfl
theorem up_body (F : ℝ → Prop) (x f : ℝ) :
    Rnd_UP_pt F x f = (F f ∧ x ≤ f ∧ ∀ g, F g → x ≤ g → f ≤ g) := rfl
theorem zr_body (F : ℝ → Prop) (x f : ℝ) :
    Rnd_ZR_pt F x f = ((0 ≤ x → Rnd_DN_pt F x f) ∧ (x ≤ 0 → Rnd_UP_pt F x f)) := rfl
theorem n_body (F : ℝ → Prop) (x f : ℝ) :
    Rnd_N_pt F x f = (F f ∧ ∀ g, F g → |f - x| ≤ |g - x|) := rfl
theorem ng_body (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (x f : ℝ) :
    Rnd_NG_pt F P x f = (Rnd_N_pt F x f ∧ (P x f ∨ ∀ f2, Rnd_N_pt F x f2 → f2 = f)) := rfl
theorem na_body (F : ℝ → Prop) (x f : ℝ) :
    Rnd_NA_pt F x f = (Rnd_N_pt F x f ∧ ∀ f2, Rnd_N_pt F x f2 → |f2| ≤ |f|) := rfl
theorem n0_body (F : ℝ → Prop) (x f : ℝ) :
    Rnd_N0_pt F x f = (Rnd_N_pt F x f ∧ ∀ f2, Rnd_N_pt F x f2 → |f| ≤ |f2|) := rfl

-- Concrete values: 3 · 2⁻¹ and −7 · 10².
local instance : ValidRadix 10 := ⟨by norm_num⟩

theorem f2r_values : F2R (FlocqFloat.mk 3 (-1) : FlocqFloat 2) = 3 / 2 ∧
    F2R (FlocqFloat.mk (-7) 2 : FlocqFloat 10) = -700 := by
  constructor <;> norm_num [F2R]

end DefsContracts
