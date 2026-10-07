import FloatSpec.src.Core.Digits

namespace DigitsDigitContracts
open FloatSpec.Core.Digits
open FloatSpec.Core.Zaux (Zpower Zpos Positive Zle_bool)

-- Digits.v:28-56: the binary length of a positive, by recursion on its digits.
-- Rocq's `Zpower_nat 2 d` is `2 ^ d`.
theorem digits_digit_contracts_check_1 : digits2_Pnat .xH = 0 := rfl
theorem digits_digit_contracts_check_2 (p : Positive) : digits2_Pnat (.xO p) = digits2_Pnat p + 1 := rfl
theorem digits_digit_contracts_check_3 (p : Positive) : digits2_Pnat (.xI p) = digits2_Pnat p + 1 := rfl
theorem digits2_bounds : ∀ n : Positive,
    (2 : Int) ^ digits2_Pnat n ≤ Zpos n ∧ Zpos n < (2 : Int) ^ (digits2_Pnat n + 1) :=
  digits2_Pnat_correct

-- Digits.v:57-720. The section radix `beta` is an `Int`; a lemma that needs its invariant
-- takes `1 < beta` as its last premise (cutover plan E5), where Rocq's `radix` record bundles
-- `2 <= beta`. `Z.quot`/`Z.rem` truncate toward zero, as `Int.tdiv`/`Int.tmod` do.
theorem digits_digit_contracts_check_4 (beta n k : Int) :
    Zdigit beta n k = Int.tmod (Int.tdiv n (Zpower beta k)) beta := rfl
theorem digits_digit_contracts_check_5 (beta : Int) (f : Int → Int) : Zsum_digit beta f 0 = 0 := rfl
theorem digits_digit_contracts_check_6 (beta : Int) (f : Int → Int) (k : Nat) :
    Zsum_digit beta f (k + 1) = Zsum_digit beta f k + f k * Zpower beta k := rfl
theorem digits_digit_contracts_check_7 (beta n k : Int) :
    Zscale beta n k =
      if Zle_bool 0 k then n * Zpower beta k else Int.tdiv n (Zpower beta (-k)) := rfl
theorem digits_digit_contracts_check_8 (beta n k1 k2 : Int) :
    Zslice beta n k1 k2 =
      if Zle_bool 0 k2 then Int.tmod (Zscale beta n (-k1)) (Zpower beta k2) else 0 := rfl

theorem digit_lt : ∀ beta n k : Int, k < 0 → Zdigit beta n k = 0 := Zdigit_lt
theorem digit_zero : ∀ beta k : Int, Zdigit beta 0 k = 0 := Zdigit_0
theorem digit_opp : ∀ beta n k : Int, Zdigit beta (-n) k = -Zdigit beta n k := Zdigit_opp
theorem digit_ge_pos : ∀ beta e n : Int, 0 ≤ n ∧ n < Zpower beta e →
    ∀ k, e ≤ k → 1 < beta → Zdigit beta n k = 0 := Zdigit_ge_Zpower_pos
theorem digit_ge : ∀ beta e n : Int, |n| < Zpower beta e →
    ∀ k, e ≤ k → 1 < beta → Zdigit beta n k = 0 := Zdigit_ge_Zpower
theorem digit_not_0_pos : ∀ beta e n : Int, 0 ≤ e →
    Zpower beta e ≤ n ∧ n < Zpower beta (e + 1) → 1 < beta → Zdigit beta n e ≠ 0 :=
  Zdigit_not_0_pos
theorem digit_not_0 : ∀ beta e n : Int, 0 ≤ e →
    Zpower beta e ≤ |n| ∧ |n| < Zpower beta (e + 1) → 1 < beta → Zdigit beta n e ≠ 0 :=
  Zdigit_not_0
theorem digit_mul_pow : ∀ beta n k k' : Int, 0 ≤ k' → 1 < beta →
    Zdigit beta (n * Zpower beta k') k = Zdigit beta n (k - k') := Zdigit_mul_pow
theorem digit_div_pow : ∀ beta n k k' : Int, 0 ≤ k → 0 ≤ k' → 1 < beta →
    Zdigit beta (Int.tdiv n (Zpower beta k')) k = Zdigit beta n (k + k') := Zdigit_div_pow
theorem digit_mod_pow : ∀ beta n k k' : Int, k < k' → 1 < beta →
    Zdigit beta (Int.tmod n (Zpower beta k')) k = Zdigit beta n k := Zdigit_mod_pow
theorem digit_mod_pow_out : ∀ beta n k k' : Int, 0 ≤ k' ∧ k' ≤ k → 1 < beta →
    Zdigit beta (Int.tmod n (Zpower beta k')) k = 0 := Zdigit_mod_pow_out
theorem sum_digit_digit : ∀ (beta n : Int) (k : Nat), 1 < beta →
    Zsum_digit beta (Zdigit beta n) k = Int.tmod n (Zpower beta k) := Zsum_digit_digit
theorem digit_ext : ∀ beta n1 n2 : Int, (∀ k, 0 ≤ k → Zdigit beta n1 k = Zdigit beta n2 k) →
    1 < beta → n1 = n2 := Zdigit_ext
theorem mod_plus_pow_digit : ∀ beta u v n : Int, 0 ≤ u * v →
    (∀ k, 0 ≤ k ∧ k < n → Zdigit beta u k = 0 ∨ Zdigit beta v k = 0) → 1 < beta →
    Int.tmod (u + v) (Zpower beta n) = Int.tmod u (Zpower beta n) + Int.tmod v (Zpower beta n) :=
  ZOmod_plus_pow_digit
theorem div_plus_pow_digit : ∀ beta u v n : Int, 0 ≤ u * v →
    (∀ k, 0 ≤ k ∧ k < n → Zdigit beta u k = 0 ∨ Zdigit beta v k = 0) → 1 < beta →
    Int.tdiv (u + v) (Zpower beta n) = Int.tdiv u (Zpower beta n) + Int.tdiv v (Zpower beta n) :=
  ZOdiv_plus_pow_digit
theorem digit_plus : ∀ beta u v : Int, 0 ≤ u * v →
    (∀ k, 0 ≤ k → Zdigit beta u k = 0 ∨ Zdigit beta v k = 0) →
    ∀ k, 1 < beta → Zdigit beta (u + v) k = Zdigit beta u k + Zdigit beta v k := Zdigit_plus
theorem digit_scale : ∀ beta n k k' : Int, 0 ≤ k' → 1 < beta →
    Zdigit beta (Zscale beta n k) k' = Zdigit beta n (k' - k) := Zdigit_scale
theorem scale_zero : ∀ beta k : Int, Zscale beta 0 k = 0 := Zscale_0
theorem same_sign_scale : ∀ beta n k : Int, 1 < beta → 0 ≤ n * Zscale beta n k :=
  Zsame_sign_scale
theorem scale_mul_pow : ∀ beta n k k' : Int, 0 ≤ k → 1 < beta →
    Zscale beta (n * Zpower beta k) k' = Zscale beta n (k + k') := Zscale_mul_pow
theorem scale_scale : ∀ beta n k k' : Int, 0 ≤ k → 1 < beta →
    Zscale beta (Zscale beta n k) k' = Zscale beta n (k + k') := Zscale_scale
theorem digit_slice : ∀ beta n k1 k2 k : Int, 0 ≤ k ∧ k < k2 → 1 < beta →
    Zdigit beta (Zslice beta n k1 k2) k = Zdigit beta n (k1 + k) := Zdigit_slice
theorem digit_slice_out : ∀ beta n k1 k2 k : Int, k2 ≤ k → 1 < beta →
    Zdigit beta (Zslice beta n k1 k2) k = 0 := Zdigit_slice_out
theorem slice_zero : ∀ beta k k' : Int, Zslice beta 0 k k' = 0 := Zslice_0
theorem same_sign_slice : ∀ beta n k k' : Int, 1 < beta → 0 ≤ n * Zslice beta n k k' :=
  Zsame_sign_slice
theorem slice_slice : ∀ beta n k1 k2 k1' k2' : Int, 0 ≤ k1' ∧ k1' ≤ k2 → 1 < beta →
    Zslice beta (Zslice beta n k1 k2) k1' k2' =
      Zslice beta n (k1 + k1') (min (k2 - k1') k2') := Zslice_slice
theorem slice_mul_pow : ∀ beta n k k1 k2 : Int, 0 ≤ k → 1 < beta →
    Zslice beta (n * Zpower beta k) k1 k2 = Zslice beta n (k1 - k) k2 := Zslice_mul_pow
theorem slice_div_pow : ∀ beta n k k1 k2 : Int, 0 ≤ k → 0 ≤ k1 → 1 < beta →
    Zslice beta (Int.tdiv n (Zpower beta k)) k1 k2 = Zslice beta n (k1 + k) k2 := Zslice_div_pow
theorem slice_scale : ∀ beta n k k1 k2 : Int, 0 ≤ k1 → 1 < beta →
    Zslice beta (Zscale beta n k) k1 k2 = Zslice beta n (k1 - k) k2 := Zslice_scale
theorem slice_div_pow_scale : ∀ beta n k k1 k2 : Int, 0 ≤ k → 1 < beta →
    Zslice beta (Int.tdiv n (Zpower beta k)) k1 k2 =
      Zscale beta (Zslice beta n k (k1 + k2)) (-k1) := Zslice_div_pow_scale
theorem plus_slice : ∀ beta n k l1 l2 : Int, 0 ≤ l1 → 0 ≤ l2 → 1 < beta →
    Zslice beta n k l1 + Zscale beta (Zslice beta n (k + l1) l2) l1 = Zslice beta n k (l1 + l2) :=
  Zplus_slice

#print axioms digits2_bounds
#print axioms digit_plus
#print axioms slice_slice

-- Truncation keeps the sign: digits of a negative number are nonpositive.
theorem digits_digit_contracts_check_9 :
    Zdigit 10 (-4321) 1 = -2 ∧ Zscale 10 (-4321) (-2) = -43 ∧ Zslice 10 (-654321) 2 3 = -543 ∧
      Zsum_digit 10 (Zdigit 10 (-654321)) 3 = -321 ∧ digits2_Pnat (.xO (.xO (.xO .xH))) = 3 := by
  decide

-- A negative modulus exponent makes `Zpower` zero and the remainder the dividend.
private theorem mod_pow_out_needs_nonneg :
    ¬ ∀ n k k' : Int, k' ≤ k → Zdigit 10 (Int.tmod n (Zpower 10 k')) k = 0 := by
  intro h
  exact absurd (h 5 0 (-1) (by decide)) (by decide)

-- The slice keeps exactly `k2` digits: index `k2` is already outside.
private theorem digit_slice_needs_bound :
    ¬ ∀ n k1 k2 k : Int, 0 ≤ k ∧ k ≤ k2 → Zdigit 10 (Zslice 10 n k1 k2) k = Zdigit 10 n (k1 + k) := by
  intro h
  exact absurd (h 123 0 1 1 (by decide)) (by decide)

#print axioms mod_pow_out_needs_nonneg

end DigitsDigitContracts
