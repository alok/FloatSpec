import FloatSpec.src.Pff.Pff2FlocqAux

/-! Executable auxiliary boundaries. Local numerical helpers are checked
against exact rational values, not presented as separate Flocq exports. -/

namespace FloatSpec.Test.PffAuxExecution

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

private def rationalValue (beta : Int) [ValidRadix beta] (p : PffFloat beta) : ℚ :=
  (p.Fnum : ℚ) * (beta : ℚ) ^ p.Fexp

private def sameFields {beta : Int} [ValidRadix beta]
    (x y : PffFloat beta) : Bool := x.Fnum == y.Fnum && x.Fexp == y.Fexp

private def check (beta : Int) [ValidRadix beta] (x y : PffFloat beta) : Bool :=
  let xv := rationalValue beta x
  let yv := rationalValue beta y
  let comparison : Int := if xv < yv then -1 else if xv > yv then 1 else 0
  pff_compare beta x y == comparison &&
    sameFields (pff_max beta x y) (if xv ≥ yv then x else y) &&
    sameFields (pff_min beta x y) (if xv ≤ yv then x else y)

private def smallGrid (beta : Int) [ValidRadix beta] : Bool :=
  (List.range 5).all fun left => (List.range 5).all fun right =>
    (List.range 3).all fun leftExponent => (List.range 3).all fun rightExponent =>
      check beta ⟨(left : Int) - 2, (leftExponent : Int) - 1⟩
        ⟨(right : Int) - 2, (rightExponent : Int) - 1⟩

/-- 225 exact-rational comparison and tie-biased selection cases. -/
theorem local_helpers_kernel : smallGrid 2 = true := by decide +kernel

private def one : PffFloat 2 := ⟨1, 0⟩
private def pair (p : PffFloat 2) : Int × Int := (p.Fnum, p.Fexp)

/-- A named identity function does not perform source normalization. -/
theorem identity_is_not_normalization :
    pair (pff_normalize 2 one) = (1, 0) ∧
    pair (PFnormalize 2 (make_bound 2 3 (-10)) 3 one) = (4, -2) := by
  decide +kernel

private def boundFields (b : Fbound) : Int × Int := (b.vNum, b.dExp)

/-- Negative precision uses the source positive-carrier fallback, not an absolute power. -/
theorem source_bound_literals :
    boundFields (make_bound 2 (-3) (-10)) = (1, 10) ∧
    boundFields (make_bound 3 2 10) = (9, 10) ∧
    boundFields bsingle = (16777216, 149) ∧
    boundFields bdouble = (9007199254740992, 1074) := by
  decide +kernel

private instance : ValidRadix 3 := ⟨by decide⟩
private instance : ValidRadix 10 := ⟨by decide⟩

private def runGrid (beta : Int) [ValidRadix beta] : IO Nat := do
  let mut count := 0
  for left in List.range 17 do
    for right in List.range 17 do
      for leftExponent in List.range 9 do
        for rightExponent in List.range 9 do
          let x : PffFloat beta := ⟨(left : Int) - 8, (leftExponent : Int) - 4⟩
          let y : PffFloat beta := ⟨(right : Int) - 8, (rightExponent : Int) - 4⟩
          unless check beta x y do
            throw (IO.userError s!"Pff auxiliary comparison failed: radix={beta}, x=({x.Fnum},{x.Fexp}), y=({y.Fnum},{y.Fexp})")
          count := count + 1
  return count

#eval do
  let count := (← runGrid 2) + (← runGrid 3) + (← runGrid 10)
  unless count == 70227 do throw (IO.userError "Pff comparison grid count changed")
  let smoke := [boundFields (make_bound 2 (-3) (-10)), boundFields bsingle,
    boundFields bdouble, pair (PFnormalize 2 (make_bound 2 3 (-10)) 3 one),
    (pff_compare 2 one ⟨3, -1⟩, 0), pair (pff_max 2 one ⟨3, -1⟩),
    pair (pff_min 2 one ⟨3, -1⟩)]
  unless smoke == [(1,10), (16777216,149), (9007199254740992,1074),
      (4,-2), (-1,0), (3,-1), (1,0)] do
    throw (IO.userError "Pff auxiliary native entry point changed")
  IO.println s!"PASS: {count} exact-rational local comparison/min/max cases and seven native entry points"

#print axioms local_helpers_kernel
#print axioms identity_is_not_normalization
#print axioms source_bound_literals

end FloatSpec.Test.PffAuxExecution
