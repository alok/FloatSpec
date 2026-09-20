import FloatSpec.src.Pff.SourceFacade

/-!
# Executable Pff boundary examples

The legacy indexed API uses type radix two for normalized neighbors, whereas
the source-shaped API consumes its explicit radix three.  These examples
deliberately retain both answers.  The bound is a valid base-three bound;
it is not a counterexample to a theorem requiring a matching base-two bound.
-/

namespace FloatSpec.Test.PffExecution

open FloatSpec.Pff

private def bound : Source.Fbound := ⟨9, 10, by decide⟩
private def input : Source.float := ⟨1, 0⟩
private def pair (p : FloatSpec.Core.Defs.FlocqFloat 2) : List Int := [p.Fnum, p.Fexp]
private def sourcePair (p : Source.float) : List Int := [p.Fnum, p.Fexp]

-- Every formerly noncomputable integer-only API is used in executable code.
private def nativeSmoke : List Int :=
  [Zpower_nat 3 2, Zpower_nat_int 3 2, _root_.nNormMin 3 2, pPred 9] ++
  pair (_root_.firstNormalPos 3 bound.toIntegrated 2) ++
  [(pffDigit 3 8 : Int), (_root_.Fdigit 3 (input.toCore 2) : Int)] ++
  pair (_root_.Fshift 3 1 (input.toCore 2)) ++
  pair (_root_.FSucc bound.toIntegrated 3 2 (input.toCore 2)) ++
  pair (_root_.FPred bound.toIntegrated 3 2 (input.toCore 2)) ++
  pair (_root_.Fnormalize 3 bound.toIntegrated 2 (input.toCore 2)) ++
  pair (_root_.FNSucc bound.toIntegrated (3 : Real) 2 (input.toCore 2)) ++
  pair (_root_.FNPred bound.toIntegrated (3 : Real) 2 (input.toCore 2)) ++
  [(_root_.digit 3 8 : Int)] ++
  pair (_root_.boundNat 3 8) ++ sourcePair (Source.boundNat 3 8) ++
  [Source.nNormMin 3 2] ++ sourcePair (Source.firstNormalPos 3 bound 2)

private def expected : List Int :=
  [9, 9, 3, 8, 3, -10, 2, 1, 3, -1, 2, 0, 0, 0, 3, -1,
    3, -1, 8, -2, 2, 1, 2, 1, 2, 3, 3, -10]

/-- Kernel reduction independently checks the native smoke-test expectations. -/
theorem integer_apis_kernel : nativeSmoke = expected := by decide +kernel

/-- info: true -/
#guard_msgs in
#eval nativeSmoke == expected

private def neighborResults : List Source.float :=
  [Source.FNSucc bound 3 2 input, Source.FNPred bound 3 2 ⟨2, 0⟩,
    Source.float.ofCore (_root_.FNSucc bound.toIntegrated (3 : Real) 2 (input.toCore 2)),
    Source.float.ofCore (_root_.FNPred bound.toIntegrated (3 : Real) 2
      ((⟨2, 0⟩ : Source.float).toCore 2))]

/-- Explicit source radix three differs observably from compatibility type radix two. -/
theorem source_and_indexed_neighbors :
    neighborResults = [⟨4, -1⟩, ⟨5, -1⟩, ⟨3, -1⟩, ⟨8, -1⟩] := by decide +kernel

/-- info: true -/
#guard_msgs in
#eval neighborResults == [⟨4, -1⟩, ⟨5, -1⟩, ⟨3, -1⟩, ⟨8, -1⟩]

/-- The explicit radix also controls normalized mantissa parity. -/
theorem source_normalized_parity :
    Source.FNodd bound 3 2 input ∧ ¬ Source.FNeven bound 3 2 input := by
  unfold Source.FNodd Source.Fodd Source.FNeven Source.Feven
  decide +kernel

#print axioms integer_apis_kernel
#print axioms source_and_indexed_neighbors
#print axioms source_normalized_parity
#print axioms Source.FSucc_toCore
#print axioms Source.FPred_toCore

end FloatSpec.Test.PffExecution
