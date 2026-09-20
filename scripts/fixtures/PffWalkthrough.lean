import FloatSpec.src.Pff.SourceFacade

/-! Run with `lake env lean --run scripts/fixtures/PffWalkthrough.lean`.
The paired PffExecution fixtures separately check these literal records in
the Lean kernel and pinned Rocq. This demo additionally executes the APIs. -/

namespace PffWalkthrough

open FloatSpec.Pff

private def bound : Source.Fbound := ⟨9, 10, by decide⟩
private def one : Source.float := ⟨1, 0⟩
private def two : Source.float := ⟨2, 0⟩
private def pair (p : Source.float) : Int × Int := (p.Fnum, p.Fexp)
private def parity (p : Source.float) : Bool × Bool :=
  (@decide (Source.FNeven bound 3 2 p)
      (by unfold Source.FNeven Source.Feven; infer_instance),
   @decide (Source.FNodd bound 3 2 p)
      (by unfold Source.FNodd Source.Fodd; infer_instance))

/-- Print the two distinct operational-radix interfaces and fail on drift. -/
def run : IO Unit := do
  let normalized := Source.Fnormalize 3 bound 2 one
  let successor := Source.FNSucc bound 3 2 one
  let predecessor := Source.FNPred bound 3 2 two
  IO.println "Pff records mean mantissa * radix^exponent."
  IO.println "The source-facing API has one explicit radix: here 3, with precision 2."
  IO.println s!"One normalizes to {pair normalized}: 3 * 3^(-1) = 1."
  IO.println s!"Its successor is {pair successor}: 4/3."
  IO.println s!"The predecessor of two is {pair predecessor}: 5/3."
  IO.println s!"Normalized one [even, odd] = {parity one}."
  unless pair normalized == (3, -1) && pair successor == (4, -1) &&
      pair predecessor == (5, -1) && parity one == (false, true) do
    throw (IO.userError "explicit-radix Pff example changed")
  let legacySuccessor := Source.float.ofCore
    (_root_.FNSucc bound.toIntegrated (3 : Real) 2 (one.toCore 2))
  let legacyPredecessor := Source.float.ofCore
    (_root_.FNPred bound.toIntegrated (3 : Real) 2 (two.toCore 2))
  IO.println "The older compatibility API is indexed by radix 2; its extra argument 3 is ignored."
  IO.println s!"It returns {pair legacySuccessor} and {pair legacyPredecessor}."
  IO.println "These are different interfaces, not competing answers for the same valid format."
  IO.println "In particular, bound 9 is valid for this base-three format, not base two."
  unless pair legacySuccessor == (3, -1) && pair legacyPredecessor == (8, -1) do
    throw (IO.userError "indexed compatibility boundary changed")

end PffWalkthrough

def main : IO Unit := PffWalkthrough.run
