import FloatSpec.src.Pff.Pff

/-! Actual Pff integer exports. Positive inputs are represented by predecessor
fields in Lean and binary positives in Rocq; no zero positive is fabricated. -/

namespace Bridge

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option pp.maxSteps 200000
set_option pp.deepTerms true

def quotientObserve (numerator denominator : Int) : List Int :=
  [Zquotient numerator denominator]

def optionFields (value : Option Positive) : List Int :=
  (match value with | none => [0, 0] | some p => [1, (nat_of_P p : Int)]) ++
    [(oZ value : Int), oZ1 value]

def positiveDivisionObserve (numerator denominator : Nat) : List Int :=
  let result := Pdiv ⟨numerator - 1⟩ ⟨denominator - 1⟩
  optionFields result.1 ++ optionFields result.2

def optionObserve (value : Nat) : List Int :=
  optionFields (nat_to_positive_option value)

def dividesObserve (value divisor : Int) : List Int :=
  [if @decide (Zdivides value divisor) (ZdividesP value divisor) then 1 else 0]

def maxDivObserve (radix value : Int) (bound : Nat) : List Int :=
  [(maxDiv radix value bound : Int)]

-- Standalone tests follow; the bridge imports only the observation prefix.
theorem signed_quotient_literals :
    [Zquotient (-7) 3, Zquotient 7 (-3), Zquotient (-7) (-3),
      Zquotient 7 3, Zquotient (-7) 0, Zquotient 0 0] = [-2, -2, 2, 2, 0, 0] := by
  decide +kernel

theorem positive_division_literals :
    [positiveDivisionObserve 1 1, positiveDivisionObserve 1 3,
      positiveDivisionObserve 7 3] =
    [[1,1,1,1,0,0,0,0], [0,0,0,0,1,1,1,1], [1,2,2,2,1,1,1,1]] := by
  decide +kernel

theorem option_literals :
    [optionObserve 0, optionObserve 1, optionObserve 7] =
    [[0,0,0,0], [1,1,1,1], [1,7,7,7]] := by
  decide +kernel

private noncomputable def classicalMaxDiv (radix value : Int) : Nat → Nat
  | 0 => 0
  | bound + 1 =>
      letI : Decidable (Zdivides value (Zpower_nat radix (bound + 1))) :=
        Classical.propDecidable _
      if Zdivides value (Zpower_nat radix (bound + 1)) then bound + 1
      else classicalMaxDiv radix value bound

/-- Constructive divisibility changes executability, not the mathematical answer. -/
theorem maxDiv_preserves_classical_definition (radix value : Int) (bound : Nat) :
    maxDiv radix value bound = classicalMaxDiv radix value bound := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      by_cases h : Zdivides value (Zpower_nat radix (bound + 1))
      · simp [maxDiv, classicalMaxDiv, h]
      · simp [maxDiv, classicalMaxDiv, h, ih]

#eval do
  unless [Zquotient (-7) 3, Zquotient 7 (-3), Zquotient (-7) (-3),
      Zquotient 7 3, Zquotient (-7) 0, Zquotient 0 0] == [-2, -2, 2, 2, 0, 0] do
    throw (IO.userError "signed/zero Pff quotient regression")
  let mut count := 0
  for numerator in List.range 64 do
    for denominator in List.range 64 do
      let p := numerator + 1
      let q := denominator + 1
      let result := Pdiv ⟨numerator⟩ ⟨denominator⟩
      unless oZ result.1 * q + oZ result.2 == p && oZ result.2 < q &&
          oZ1 result.1 == (oZ result.1 : Int) && oZ1 result.2 == (oZ result.2 : Int) do
        throw (IO.userError s!"Pff positive division regression: {p}/{q}")
      count := count + 1
  IO.println s!"PASS: six signed/zero quotient literals and {count} positive division/option cases"

#eval do
  unless [maxDiv 2 8 7, maxDiv 2 0 7, maxDiv 0 7 7, maxDiv 0 0 7,
      maxDiv (-2) (-8) 7, maxDiv 1 7 7, maxDiv 3 81 2] == [3,7,0,7,3,7,2] do
    throw (IO.userError "Pff bounded divisibility regression")
  unless [dividesObserve 0 0, dividesObserve 1 0, dividesObserve 6 3,
      dividesObserve 3 6, dividesObserve (-6) (-3)] == [[1],[0],[1],[0],[1]] do
    throw (IO.userError "Pff divisibility argument/zero regression")
  IO.println "PASS: seven bounded-divisibility and five signed/zero divisibility literals"

#print axioms signed_quotient_literals
#print axioms positive_division_literals
#print axioms option_literals
#print axioms Zquotient
#print axioms Pdiv
#print axioms Pdiv_correct
-- The transcribed Pdiv and Zquotient equal natural division and `Int.tdiv`.
#print axioms Pdiv_eq_PdivNat
#print axioms Zquotient_eq_tdiv
-- Choice enters these only through erased proof fields; their decisions run.
#print axioms ZdividesP
#print axioms maxDiv
#print axioms maxDiv_preserves_classical_definition

end Bridge
