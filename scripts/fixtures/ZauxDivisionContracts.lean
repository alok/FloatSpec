import FloatSpec.src.Core.Zaux

namespace ZauxDivisionContracts
open FloatSpec.Core.Zaux

-- Rocq floor division/modulo agrees with Lean's Euclidean operations on the
-- nonnegative divisor domain of these two source contracts, not universally.
example : ∀ n a b : Int, 0 < a → 0 ≤ b → n % (a * b) % b = n % b := Zmod_mod_mult
example : ∀ n a b : Int, 0 ≤ a → 0 ≤ b →
    (n % (a * b)) / a = (n / a) % b := Zdiv_mod_mult
example (a b : Int) (h : 0 ≤ b) : a.fdiv b = a / b := Int.fdiv_eq_ediv_of_nonneg a h
example (a b : Int) (h : 0 ≤ b) : a.fmod b = a % b := Int.fmod_eq_emod_of_nonneg a h

-- The source Z.quot / Z.rem are truncating division and remainder, including
-- negative and zero divisors. No nonzero-divisor premise is added here.
example : ∀ a b : Int, a.tmod b = a - a.tdiv b * b := ZOmod_eq
example : ∀ n a b : Int, (n.tmod (a * b)).tmod b = n.tmod b := ZOmod_mod_mult
example : ∀ n a b : Int, (n.tmod (a * b)).tdiv a = (n.tdiv a).tmod b := ZOdiv_mod_mult
example (a b : Int) (h : |a| < b) : a.tdiv b = 0 :=
  ZOdiv_small_abs a b (by simpa using h)
example (a b : Int) (h : |a| < b) : a.tmod b = a :=
  ZOmod_small_abs a b (by simpa using h)
example : ∀ a b c : Int, 0 ≤ a * b →
    (a + b).tdiv c = a.tdiv c + b.tdiv c + (a.tmod c + b.tmod c).tdiv c := ZOdiv_plus

-- The next four source declarations use products to express a shared sign.
-- Zero is neutral, so transitivity needs precisely the source's side condition.
theorem same_sign_trans_contract : ∀ v u w : Int, v ≠ 0 →
    0 ≤ u * v → 0 ≤ v * w → 0 ≤ u * w := Zsame_sign_trans
theorem same_sign_trans_weak_contract : ∀ v u w : Int, (v = 0 → w = 0) →
    0 ≤ u * v → 0 ≤ v * w → 0 ≤ u * w := Zsame_sign_trans_weak
theorem same_sign_imp_contract : ∀ u v : Int,
    (0 < u → 0 ≤ v) → (0 < -u → 0 ≤ -v) → 0 ≤ u * v := Zsame_sign_imp
theorem same_sign_odiv_contract : ∀ u v : Int, 0 ≤ v →
    0 ≤ u * u.tdiv v := Zsame_sign_odiv

#print axioms same_sign_trans_contract
#print axioms same_sign_trans_weak_contract
#print axioms same_sign_imp_contract
#print axioms same_sign_odiv_contract

-- Both same-sign transitivity laws fail without their zero side condition:
-- the middle factor 0 connects 1 and -1, although their product is negative.
private theorem same_sign_trans_needs_zero_condition :
    ¬ ∀ v u w : Int, 0 ≤ u * v → 0 ≤ v * w → 0 ≤ u * w := by
  intro h
  exact (by decide : ¬ 0 ≤ (1 : Int) * (-1)) (h 0 1 (-1) (by decide) (by decide))

#print axioms same_sign_trans_needs_zero_condition

-- A negative divisor can reverse the sign; zero remains a permitted divisor.
private theorem same_sign_odiv_needs_nonnegative_divisor :
    ¬ ∀ u v : Int, 0 ≤ u * u.tdiv v := by
  intro h
  exact (by decide : ¬ 0 ≤ (1 : Int) * (1 : Int).tdiv (-1)) (h 1 (-1))

#print axioms same_sign_odiv_needs_nonnegative_divisor

example : (7 : Int) / (-3) = -2 ∧ (7 : Int) % (-3) = 1 := by decide +kernel
example : (7 : Int).fdiv (-3) = -3 ∧ (7 : Int).fmod (-3) = -2 := by decide +kernel
example : (-7 : Int).tdiv 3 = -2 ∧ (-7 : Int).tmod 3 = -1 := by decide +kernel
example (a : Int) : a.tdiv 0 = 0 ∧ a.tmod 0 = a := by simp

-- With opposite signs (-2 and 1), truncating quotient addition can fail.
private theorem quotient_addition_needs_sign_condition :
    ¬ ∀ a b c : Int,
      (a + b).tdiv c = a.tdiv c + b.tdiv c + (a.tmod c + b.tmod c).tdiv c := by
  intro h
  exact (by decide : ¬ ((-2 : Int) + 1).tdiv 2 =
    (-2 : Int).tdiv 2 + (1 : Int).tdiv 2 + ((-2 : Int).tmod 2 + (1 : Int).tmod 2).tdiv 2)
    (h (-2) 1 2)

#print axioms quotient_addition_needs_sign_condition

#eval do
  let mut checked := 0
  for ni in List.range 17 do
    for ai in List.range 9 do
      for bi in List.range 9 do
        let n := Int.ofNat ni - 8
        let a := Int.ofNat ai - 4
        let b := Int.ofNat bi - 4
        unless n.tmod a == n - n.tdiv a * a &&
            (n.tmod (a*b)).tmod b == n.tmod b &&
            (n.tmod (a*b)).tdiv a == (n.tdiv a).tmod b do
          throw (IO.userError s!"truncating identity regression: {n}, {a}, {b}")
        if 0 ≤ a && 0 ≤ b then
          unless (n % (a*b)) / a == (n / a) % b do
            throw (IO.userError "nonnegative floor/Euclidean contract")
        if 0 ≤ n*a then
          unless (n+a).tdiv b == n.tdiv b + a.tdiv b + (n.tmod b + a.tmod b).tdiv b do
            throw (IO.userError "same-sign quotient addition contract")
        if n != 0 && 0 ≤ a*n && 0 ≤ n*b then
          unless 0 ≤ a*b do
            throw (IO.userError "same-sign transitivity contract")
        if (n != 0 || b == 0) && 0 ≤ a*n && 0 ≤ n*b then
          unless 0 ≤ a*b do
            throw (IO.userError "weak same-sign transitivity contract")
        if (n ≤ 0 || 0 ≤ a) && (-n ≤ 0 || 0 ≤ -a) then
          unless 0 ≤ n*a do
            throw (IO.userError "same-sign implication contract")
        if 0 ≤ a then
          unless 0 ≤ n * n.tdiv a do
            throw (IO.userError "same-sign quotient contract")
        checked := checked + 1
  IO.println s!"PASS: {checked} signed division/sign inputs; exact source domains and zero cases"

end ZauxDivisionContracts
