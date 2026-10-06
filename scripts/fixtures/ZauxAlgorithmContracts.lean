import FloatSpec.src.Core.Zaux

namespace ZauxAlgorithmContracts
open FloatSpec.Core.Zaux

-- Conditional negation laws (Zaux.v:776-816). Rocq's `Z.abs` is `|·|`.
theorem cond_zero : ∀ sx : Bool, cond_Zopp sx 0 = 0 := cond_Zopp_0
theorem cond_negb : ∀ (x : Bool) (y : Int), cond_Zopp (!x) y = -cond_Zopp x y := cond_Zopp_negb
theorem cond_abs : ∀ (b : Bool) (m : Int), |cond_Zopp b m| = |m| := abs_cond_Zopp
theorem cond_lt : ∀ m : Int, cond_Zopp (Zlt_bool m 0) m = |m| := cond_Zopp_Zlt_bool
theorem cond_eq : ∀ (s : Bool) (m n : Int),
    Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n) := Zeq_bool_cond_Zopp

-- Fast power (Zaux.v:824-849): the body squares along the exponent's binary digits.
-- Rocq's `Z.square x` is `x * x`; Lean writes `x ^ 2`.
example (v : Int) : Zfast_pow_pos v .xH = v := rfl
example (v : Int) (e : Positive) : Zfast_pow_pos v (.xO e) = Zfast_pow_pos v e ^ 2 := rfl
example (v : Int) (e : Positive) : Zfast_pow_pos v (.xI e) = v * Zfast_pow_pos v e ^ 2 := rfl
theorem fast_pow : ∀ (v : Int) (e : Positive), Zfast_pow_pos v e = Zpower_pos v e :=
  Zfast_pow_pos_correct

-- Faster division (Zaux.v:851-976). `Z.div_eucl` is the floor pair `Z_div_eucl`.
theorem div_eucl_unique : ∀ a b : Int, Z_div_eucl a b = (a.fdiv b, a.fmod b) := Zdiv_eucl_unique
-- `Zpos_div_eucl_aux1` recurses on the divisor's digits exactly as the source does.
example (a : Positive) : Zpos_div_eucl_aux1 a .xH = (Zpos a, 0) := rfl
example (a b : Positive) :
    Zpos_div_eucl_aux1 a (.xI b) = Z_pos_div_eucl a (Zpos (.xI b)) := rfl
example (b : Positive) : Zpos_div_eucl_aux1 .xH (.xO b) = (0, Zpos .xH) := rfl
example (a b : Positive) :
    Zpos_div_eucl_aux1 (.xO a) (.xO b) = (let (q, r) := Zpos_div_eucl_aux1 a b; (q, 2 * r)) := rfl
example (a b : Positive) :
    Zpos_div_eucl_aux1 (.xI a) (.xO b) =
      (let (q, r) := Zpos_div_eucl_aux1 a b; (q, 2 * r + 1)) := rfl
theorem aux1_correct : ∀ a b : Positive,
    Zpos_div_eucl_aux1 a b = Z_pos_div_eucl a (Zpos b) := Zpos_div_eucl_aux1_correct
theorem aux_correct : ∀ a b : Positive,
    Zpos_div_eucl_aux a b = Z_pos_div_eucl a (Zpos b) := Zpos_div_eucl_aux_correct
theorem fast_div : ∀ a b : Int, Zfast_div_eucl a b = Z_div_eucl a b := Zfast_div_eucl_correct

-- The zero-divisor branch tests `1 mod 0`; both systems define it as 1, so `(0, a)`.
example : Int.fmod 1 0 = 1 ∧ Zfast_div_eucl 7 0 = (0, 7) ∧ Zfast_div_eucl (-7) 0 = (0, -7) := by
  decide +kernel

-- Iteration (Zaux.v:978-1027). Flocq's `iter_nat` applies `f` first.
example {A : Type} (f : A → A) (n : Nat) (x : A) : iter_nat f (n + 1) x = iter_nat f n (f x) := rfl
theorem iter_plus : ∀ {A : Type} (f : A → A) (p q : Nat) (x : A),
    iter_nat f (p + q) x = iter_nat f p (iter_nat f q x) := @iter_nat_plus
theorem iter_S : ∀ {A : Type} (f : A → A) (p : Nat) (x : A),
    iter_nat f (p + 1) x = f (iter_nat f p x) := @iter_nat_S
theorem iter_pos_eq : ∀ {A : Type} (f : A → A) (p : Positive) (x : A),
    iter_pos f p x = iter_nat f (positiveToNat p) x := @iter_pos_nat

#print axioms fast_div
#print axioms aux1_correct
#print axioms fast_pow
#print axioms iter_plus
#print axioms cond_lt

-- `cond_Zopp_Zlt_bool` negates exactly the negative inputs: the swapped test fails at 1.
private theorem cond_lt_needs_orientation :
    ¬ ∀ m : Int, cond_Zopp (Zlt_bool 0 m) m = |m| := by
  intro h
  exact absurd (h 1) (by decide)

-- Moving a conditional negation across equality must negate the other side.
private theorem cond_eq_needs_negation :
    ¬ ∀ (s : Bool) (m n : Int), Zeq_bool (cond_Zopp s m) n = Zeq_bool m n := by
  intro h
  exact absurd (h true 1 (-1)) (by decide)

-- `Zfast_div_eucl` is floor division, not Lean's default Euclidean `/` and `%`.
private theorem fast_div_is_not_default_division :
    Zfast_div_eucl 7 (-3) = (-3, -2) ∧ ((7 : Int) / (-3), (7 : Int) % (-3)) = (-2, 1) := by
  decide +kernel

#print axioms cond_lt_needs_orientation
#print axioms cond_eq_needs_negation
#print axioms fast_div_is_not_default_division

-- Every algorithm against an independent formula, including 2^64-scale operands.
#eval do
  let small := (List.range 17).map fun k => Int.ofNat k - 8
  let values := small ++ [-2^64 - 1, -2^63, 2^63 - 1, 2^64 + 1]
  let mut checked := 0
  for x in values do
    for b in [false, true] do
      unless cond_Zopp b x == (if b then -x else x) && |cond_Zopp b x| == |x| do
        throw (IO.userError s!"conditional negation: {b}, {x}")
    unless cond_Zopp (Zlt_bool x 0) x == |x| do
      throw (IO.userError s!"conditional absolute value: {x}")
    for y in values do
      -- Floor division, remainder with the divisor's sign; (0, a) for divisor zero.
      let q := if y = 0 then 0 else x.fdiv y
      unless Zfast_div_eucl x y == (q, x - y * q) &&
          (y == 0 || (x - y * q == 0 || (0 < x - y * q) == (0 < y))) do
        throw (IO.userError s!"fast division: {x}, {y}")
      checked := checked + 1
  for v in small do
    for n in List.range 20 do
      unless Zfast_pow_pos v (Pos_of_nat (n + 1)) == v ^ (n + 1) do
        throw (IO.userError s!"fast power: {v}, {n + 1}")
      unless iter_nat (· * 2 + 1) n v == (v + 1) * 2 ^ n - 1 do
        throw (IO.userError s!"iteration: {v}, {n}")
  IO.println s!"PASS: {checked} signed division pairs; sign, power and iteration laws"

end ZauxAlgorithmContracts
