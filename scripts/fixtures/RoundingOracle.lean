import FloatSpec.src.IEEE754.Bits

/-! Independent exhaustive selection oracle for a small binary format.
The oracle enumerates representable values, filters by the requested direction,
then minimizes exact integer distance. It does not call Flocq's rounding
decisions, shifts, digit counts, or exponent selection. NaNs, infinities and
signed-zero identity are outside this finite-value oracle's claim. -/

namespace RoundingOracle

private def positives : List (Int × Bool) :=
  [(1, false), (2, true), (3, false)] ++
    (List.range 6).flatMap fun shift =>
      [4, 5, 6, 7].map fun m => (m * (2 : Int) ^ shift, m % 2 == 0)

private def candidates : List (Int × Bool) :=
  positives.map (fun (v, even) => (-v, even)) ++ [(0, true)] ++ positives

private def allowed (mode : RoundingMode) (n v : Int) : Bool :=
  match mode with
  | .RNE | .RNA => true
  | .RTN => 16 * v ≤ n
  | .RTP => n ≤ 16 * v
  | .RTZ => if n < 0 then n ≤ 16 * v else 16 * v ≤ n

private def better (mode : RoundingMode) (n : Int) (a b : Int × Bool) : Bool :=
  let da := (16 * a.1 - n).natAbs
  let db := (16 * b.1 - n).natAbs
  da < db || (da == db && match mode with
    | .RNE => a.2 && !b.2
    | .RNA => a.1.natAbs > b.1.natAbs
    | _ => false)

private def oracle (mode : RoundingMode) (n : Int) : Option Int :=
  let selected := candidates.foldl (fun (best : Option (Int × Bool)) next =>
    if !allowed mode n next.1 then best
    else match best with
      | none => some next
      | some old => if better mode n next old then some next else best) none
  selected.map Prod.fst

private def observed (mode : RoundingMode) (n : Int) : Option Int :=
  if n = 0 then some 0
  else match binary_round (prec := 3) (emax := 4) mode (n < 0) n.natAbs (-8) with
  | .S754_zero _ => some 0
  | .S754_finite sign m e =>
      if -4 ≤ e then
        let v : Int := m * (2 : Int) ^ (e + 4).toNat
        some (if sign then -v else v)
      else none
  | _ => none

private def modes : List RoundingMode := [.RNE, .RTZ, .RTN, .RTP, .RNA]

private def modeLabel : RoundingMode → String
  | .RNE => "RNE"
  | .RTZ => "RTZ"
  | .RTN => "RTN"
  | .RTP => "RTP"
  | .RNA => "RNA"

/-- Distances are in 2^-8 input units; outputs are 2^-4 units. These examples
pin normal and subnormal ties, including mantissa parity after normalization. -/
theorem boundary_oracle :
    oracle .RNE 8 = some 0 ∧ oracle .RNA 8 = some 1 ∧
    oracle .RNE 288 = some 16 ∧ oracle .RNE 352 = some 24 ∧
    oracle .RNE (-352) = some (-24) ∧ oracle .RTN (-1) = some (-1) ∧
    oracle .RTP 1 = some 1 ∧ oracle .RNE (-3328) = some (-192) ∧
    oracle .RNA (-3328) = some (-224) := by
  decide +kernel

/-- Closed kernel checks around zero, minimum normal, and normal ties. -/
theorem boundary_agreement :
    (modes.all fun mode =>
      [-3584, -3328, -352, -288, -65, -64, -63, -8, -1, 0, 1, 8, 63, 64, 65, 288, 352, 3328, 3584].all
        fun n => observed mode n == oracle mode n) = true := by
  decide +kernel

/-- Execute every 2^-8 input from -14 through 14 in all five modes. A mismatch
throws an IO error with its replayable mode and numerator, not merely a trace. -/
private def runGrid : IO Unit := do
  for mode in modes do
    for k in List.range 7169 do
      let n : Int := k - 3584
      let actual := observed mode n
      let expected := oracle mode n
      unless actual == expected do
        throw <| IO.userError s!"rounding oracle mismatch: mode={modeLabel mode}, numerator={n}, observed={actual}, expected={expected}"
  IO.println "PASS: 35,845 independent finite rounding-oracle cases; 95 kernel boundary cases"

#eval runGrid

end RoundingOracle
