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
        checked := checked + 1
  IO.println s!"PASS: {checked} signed division inputs; exact source domains and zero cases"

end ZauxDivisionContracts
