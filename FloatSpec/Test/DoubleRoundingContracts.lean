import FloatSpec.src.Prop.Double_rounding

/-! Paired source-body and exported-premise guards. These check the named
contracts, not every theorem of the surrounding module. -/

open FloatSpec.Core.Generic_fmt FloatSpec.Core.Defs
namespace FloatSpec.Test.DoubleRoundingContracts

variable (beta : Int) [ValidRadix beta]
variable (fexp1 fexp2 : Int → Int) (choice1 choice2 : Int → Bool)

/-- Literal source body guard. -/
theorem equality_contract (x : Real) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x =
      (roundR beta fexp1 (Znearest choice1)
          (roundR beta fexp2 (Znearest choice2) x) =
        roundR beta fexp1 (Znearest choice1) x) := rfl

/-- Literal source body guard. -/
theorem midpoint_contract (x : Real) : midp beta fexp1 x =
    roundR beta fexp1 rnd_floor x + (1 / 2) * FloatSpec.Core.Ulp.ulp beta fexp1 x := rfl
/-- Literal source body guard. -/
theorem upper_midpoint_contract (x : Real) : midp' beta fexp1 x =
    roundR beta fexp1 rnd_ceil x - (1 / 2) * FloatSpec.Core.Ulp.ulp beta fexp1 x := rfl

/-- Literal source body guard. -/
theorem mult_hyp_contract : round_round_mult_hyp fexp1 fexp2 =
    ((∀ ex ey, fexp2 (ex + ey) ≤ fexp1 ex + fexp1 ey) ∧
     (∀ ex ey, fexp2 (ex + ey - 1) ≤ fexp1 ex + fexp1 ey)) := rfl

/-- Literal source body guard. -/
theorem plus_hyp_contract : round_round_plus_hyp fexp1 fexp2 =
    ((∀ ex ey, fexp1 (ex + 1) - 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
     (∀ ex ey, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
     (∀ ex ey, fexp1 ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
     (∀ ex ey, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)) := rfl

/-- Literal source body guard. -/
theorem plus_ge3_hyp_contract : round_round_plus_radix_ge_3_hyp fexp1 fexp2 =
    ((∀ ex ey, fexp1 (ex + 1) ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
     (∀ ex ey, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
     (∀ ex ey, fexp1 ex ≤ ey → fexp2 ex ≤ fexp1 ey) ∧
     (∀ ex ey, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)) := rfl

/-- Literal source body guard. -/
theorem sqrt_hyp_contract : round_round_sqrt_hyp fexp1 fexp2 =
    ((∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
     (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
     (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 2)) := rfl

/-- Literal source body guard. -/
theorem sqrt_ge4_hyp_contract : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2 =
    ((∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
     (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
     (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 1)) := rfl

/-- Literal source body guard. -/
theorem div_hyp_contract : round_round_div_hyp fexp1 fexp2 =
    ((∀ ex, fexp2 ex ≤ fexp1 ex - 1) ∧
     (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
       fexp1 (ex - ey) ≤ ex - ey + 1 → fexp2 (ex - ey) ≤ fexp1 ex - ey) ∧
     (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
       fexp1 (ex - ey + 1) ≤ ex - ey + 1 + 1 →
       fexp2 (ex - ey + 1) ≤ fexp1 ex - ey) ∧
     (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
       fexp1 (ex - ey) ≤ ex - ey →
       fexp2 (ex - ey) ≤ fexp1 (ex - ey) + fexp1 ey - ey) ∧
     (∀ ex ey, fexp1 ex < ex → fexp1 ey < ey →
       fexp1 (ex - ey) = ex - ey + 1 →
       fexp2 (ex - ey) ≤ ex - ey - ey + fexp1 ey)) := rfl

/-- Typed client with exactly the reviewed source premises. -/
theorem mult_aux_client (h : round_round_mult_hyp fexp1 fexp2)
    (x y : Real) (hx : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) : FloatSpec.Core.Generic_fmt.generic_format beta fexp2 (x * y) :=
  round_round_mult_aux beta fexp1 fexp2 ValidRadix.valid h x y hx hy

/-- Typed client with exactly the reviewed source premises. -/
theorem mult_client (rnd : Real → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd]
    (h : round_round_mult_hyp fexp1 fexp2)
    (x y : Real) (hx : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    roundR beta fexp1 rnd (roundR beta fexp2 rnd (x * y)) =
      roundR beta fexp1 rnd (x * y) :=
  round_round_mult beta rnd fexp1 fexp2 ValidRadix.valid h x y hx hy

variable [Valid_exp fexp1] [Valid_exp fexp2]

/-- Typed client with exactly the reviewed source premises. -/
theorem plus_client (h : round_round_plus_hyp fexp1 fexp2)
    (x y : Real) (hx : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) :=
  round_round_plus beta fexp1 fexp2 choice1 choice2 ValidRadix.valid h x y hx hy

/-- Typed client with exactly the reviewed source premises. -/
theorem minus_client (h : round_round_plus_hyp fexp1 fexp2)
    (x y : Real) (hx : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) :=
  round_round_minus beta fexp1 fexp2 choice1 choice2 ValidRadix.valid h x y hx hy

/-- Typed client with exactly the reviewed source premises. -/
theorem sqrt_client (h : round_round_sqrt_hyp fexp1 fexp2)
    (x : Real) (hx : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) :=
  round_round_sqrt beta fexp1 fexp2 choice1 choice2 ValidRadix.valid h x hx

/-- Typed client with exactly the reviewed source premises. -/
theorem div_client (heven : ∃ n : Int, beta = 2 * n)
    (h : round_round_div_hyp fexp1 fexp2)
    (x y : Real) (hne : y ≠ 0) (hx : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 x)
    (hy : FloatSpec.Core.Generic_fmt.generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) :=
  round_round_div beta fexp1 fexp2 choice1 choice2 ValidRadix.valid heven h x y hne hx hy

/-- The radix-at-least-four square-root condition genuinely saves one radix digit
of precision in this FLX-shaped exponent example. -/
theorem sqrt_radix_four_gap :
    round_round_sqrt_radix_ge_4_hyp (fun exponent => exponent - 1)
      (fun exponent => exponent - 3) ∧
    ¬ round_round_sqrt_hyp (fun exponent => exponent - 1)
      (fun exponent => exponent - 3) := by
  dsimp only [round_round_sqrt_radix_ge_4_hyp, round_round_sqrt_hyp]
  constructor
  · exact ⟨by intro exponent; omega, by intro exponent; omega,
      by intro exponent h; omega⟩
  · intro h
    have contradiction := h.2.2 0 (by decide)
    omega

#print axioms sqrt_radix_four_gap
#print axioms mult_aux_client
#print axioms mult_client
#print axioms plus_client
#print axioms minus_client
#print axioms sqrt_client
#print axioms div_client
end FloatSpec.Test.DoubleRoundingContracts
