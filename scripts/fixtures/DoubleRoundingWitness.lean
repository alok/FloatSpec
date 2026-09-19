import FloatSpec.src.IEEE754.Bits

/-! A concrete reason the hypotheses in Prop/Double_rounding matter.
The input 73 * 2^-6 is just above the three-bit midpoint 9 * 2^-3.
Rounding it to four bits first lands exactly on that midpoint, changing the
nearest-even result at three bits. This is not a counterexample to Flocq's
conditional innocuous-double-rounding theorems. -/

namespace DoubleRoundingWitness

private def observe : StandardFloat → List Int
  | .S754_finite s m e => [if s then 1 else 0, m, e]
  | _ => []

private def direct (s : Bool) : StandardFloat :=
  binary_round (prec := 3) (emax := 10) .RNE s 73 (-6)

private def viaFour (s : Bool) : StandardFloat :=
  match binary_round (prec := 4) (emax := 10) .RNE s 73 (-6) with
  | .S754_finite sign m e => binary_round (prec := 3) (emax := 10) .RNE sign m e
  | x => x

/-- Both signs expose the same midpoint-rounding hazard. -/
theorem counterexample :
    observe (direct false) = [0,5,-2] ∧ observe (viaFour false) = [0,4,-2] ∧
    observe (direct true) = [1,5,-2] ∧ observe (viaFour true) = [1,4,-2] := by
  decide +kernel

#eval [observe (direct false), observe (viaFour false),
  observe (direct true), observe (viaFour true)]

end DoubleRoundingWitness
