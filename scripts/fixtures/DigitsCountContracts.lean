import FloatSpec.src.Core.Digits

namespace DigitsCountContracts
open FloatSpec.Core.Digits
open FloatSpec.Core.Zaux (Zpower Zpos Positive Zlt_bool zview cond_Zopp)

-- Digits.v:722-1176. As in the digit laws, `1 < beta` is the last premise where needed.
-- `Zdigits_aux` takes the section variable `p` first. `Zdigits` reads Rocq's `Z0`/`Zpos`/`Zneg`
-- through `zview`.
theorem digits_count_contracts_check_1 (beta p nb pow : Int) : Zdigits_aux beta p nb pow 0 = nb := rfl
theorem digits_count_contracts_check_2 (beta p nb pow : Int) (n : Nat) :
    Zdigits_aux beta p nb pow (n + 1) =
      if Zlt_bool p pow then nb else Zdigits_aux beta p (nb + 1) (beta * pow) n := rfl
theorem digits_count_contracts_check_3 (beta n : Int) :
    Zdigits beta n =
      match zview n with
      | .Z0 => 0
      | .Zneg p => Zdigits_aux beta (Zpos p) 1 beta (digits2_Pnat p)
      | .Zpos p => Zdigits_aux beta n 1 beta (digits2_Pnat p) := rfl

theorem correct : ∀ beta n : Int, 1 < beta →
    Zpower beta (Zdigits beta n - 1) ≤ |n| ∧ |n| < Zpower beta (Zdigits beta n) := Zdigits_correct
theorem unique : ∀ beta n d : Int,
    Zpower beta (d - 1) ≤ |n| ∧ |n| < Zpower beta d → 1 < beta → Zdigits beta n = d :=
  Zdigits_unique
theorem abs' : ∀ beta n : Int, Zdigits beta |n| = Zdigits beta n := Zdigits_abs
theorem opp : ∀ beta n : Int, Zdigits beta (-n) = Zdigits beta n := Zdigits_opp
theorem cond_opp : ∀ (beta : Int) (s : Bool) (n : Int), Zdigits beta (cond_Zopp s n) = Zdigits beta n :=
  Zdigits_cond_Zopp
theorem gt_0 : ∀ beta n : Int, n ≠ 0 → 0 < Zdigits beta n := Zdigits_gt_0
theorem ge_0 : ∀ beta n : Int, 0 ≤ Zdigits beta n := Zdigits_ge_0
theorem digit_out : ∀ beta n k : Int, Zdigits beta n ≤ k → 1 < beta → Zdigit beta n k = 0 :=
  Zdigit_out
theorem digit_digits : ∀ beta n : Int, n ≠ 0 → 1 < beta → Zdigit beta n (Zdigits beta n - 1) ≠ 0 :=
  Zdigit_digits
theorem slice : ∀ beta n k l : Int, 0 ≤ l → 1 < beta → Zdigits beta (Zslice beta n k l) ≤ l :=
  Zdigits_slice
theorem mult_Zpower : ∀ beta m e : Int, m ≠ 0 → 0 ≤ e → 1 < beta →
    Zdigits beta (m * Zpower beta e) = Zdigits beta m + e := Zdigits_mult_Zpower
theorem of_Zpower : ∀ beta e : Int, 0 ≤ e → 1 < beta → Zdigits beta (Zpower beta e) = e + 1 :=
  Zdigits_Zpower
theorem le : ∀ beta x y : Int, 0 ≤ x → x ≤ y → 1 < beta → Zdigits beta x ≤ Zdigits beta y :=
  Zdigits_le
theorem lt : ∀ beta x y : Int, 0 ≤ y → Zdigits beta x < Zdigits beta y → 1 < beta → x < y :=
  lt_Zdigits
theorem pow_le : ∀ beta e x : Int, e < Zdigits beta x → 1 < beta → Zpower beta e ≤ |x| :=
  Zpower_le_Zdigits
theorem le_pow : ∀ beta e x : Int, |x| < Zpower beta e → 1 < beta → Zdigits beta x ≤ e :=
  Zdigits_le_Zpower
theorem pow_gt : ∀ beta e x : Int, Zdigits beta x ≤ e → 1 < beta → |x| < Zpower beta e :=
  Zpower_gt_Zdigits
theorem gt_pow : ∀ beta e x : Int, Zpower beta e ≤ |x| → 1 < beta → e < Zdigits beta x :=
  Zdigits_gt_Zpower
theorem mult_strong : ∀ beta x y : Int, 0 ≤ x → 0 ≤ y → 1 < beta →
    Zdigits beta (x + y + x * y) ≤ Zdigits beta x + Zdigits beta y := Zdigits_mult_strong
theorem mult : ∀ beta x y : Int, 1 < beta → Zdigits beta (x * y) ≤ Zdigits beta x + Zdigits beta y :=
  Zdigits_mult
theorem mult_ge : ∀ beta x y : Int, x ≠ 0 → y ≠ 0 → 1 < beta →
    Zdigits beta x + Zdigits beta y - 1 ≤ Zdigits beta (x * y) := Zdigits_mult_ge
-- Rocq's `/` on `Z` floors; for the positive divisor Lean's Euclidean `/` agrees.
theorem div_Zpower : ∀ beta m e : Int, 0 ≤ m → 0 ≤ e ∧ e ≤ Zdigits beta m → 1 < beta →
    Zdigits beta (m / Zpower beta e) = Zdigits beta m - e := Zdigits_div_Zpower
theorem succ_le : ∀ beta x : Int, 0 ≤ x → 1 < beta → Zdigits beta (x + 1) ≤ Zdigits beta x + 1 :=
  Zdigits_succ_le
theorem binary_length : ∀ m : Positive,
    ((digits2_Pnat m + 1 : Nat) : Int) = Zdigits 2 (Zpos m) := Z_of_nat_S_digits2_Pnat
-- `Zdigits2` is SpecFloat's binary digit count.
theorem binary_digits : ∀ n : Int, Zdigits2 n = Zdigits 2 n := Zdigits2_Zdigits

#print axioms correct
#print axioms mult_ge
#print axioms div_Zpower

-- Counts by sign and at powers: 999 has three decimal digits, 1000 four.
theorem digits_count_contracts_check_4 :
    Zdigits 10 0 = 0 ∧ Zdigits 10 (-999) = 3 ∧ Zdigits 10 1000 = 4 ∧ Zdigits 2 (2 ^ 64) = 65 ∧
      Zdigits 16 (-(16 ^ 32 - 1)) = 32 := by
  decide +kernel

-- The radix invariant is needed: at radix 1 the counter runs out of fuel instead.
private theorem correct_needs_radix : ¬ ∀ n : Int,
    Zpower 1 (Zdigits 1 n - 1) ≤ |n| ∧ |n| < Zpower 1 (Zdigits 1 n) := by
  intro h
  exact absurd (h 3) (by decide)

-- `Zdigits_le` needs a nonnegative smaller argument: -1000 has more digits than 1.
private theorem le_needs_nonneg : ¬ ∀ x y : Int, x ≤ y → Zdigits 10 x ≤ Zdigits 10 y := by
  intro h
  exact absurd (h (-1000) 1 (by decide)) (by decide)

#print axioms correct_needs_radix

end DigitsCountContracts
