import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Exact eighth-integer oracle. The expected result uses signed integer
division and distance/parity, not the implementation's shifts or mantissas.
The oracle checks integer values; signed zero and NaN payloads are covered by
the separate bit-level differential bridge. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option exponentiation.threshold 5000

namespace IntegerRounding

private instance : Prec_gt_0 (24 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (24 : Int) (128 : Int) := ⟨by decide⟩

private def expected (mode : RoundingMode) (numerator : Int) : Int :=
  let lower := numerator / 8
  let remainder := numerator % 8
  let upper := lower + if remainder = 0 then 0 else 1
  match mode with
  | .RTN => lower
  | .RTP => upper
  | .RTZ => if numerator < 0 then upper else lower
  | .RNE =>
      if remainder < 4 then lower else if 4 < remainder then upper
      else if lower % 2 = 0 then lower else upper
  | .RNA =>
      if remainder < 4 then lower else if 4 < remainder then upper
      else if numerator < 0 then lower else upper

private def check (mode : RoundingMode) (numerator : Int) : Bool :=
  let x := Binary.B2BSN (Binary.normalize (prec:=24) (emax:=128) .RNE numerator (-3) false)
  let y := BinarySingleNaN.Bnearbyint mode x
  let z := BinarySingleNaN.Bnearbyint mode y
  decide (BinarySingleNaN.Btrunc x = expected .RTZ numerator) &&
    decide (BinarySingleNaN.Btrunc y = expected mode numerator) &&
    decide (binarySingleNaNFloatToStandardFloat z = binarySingleNaNFloatToStandardFloat y)

private def cases : List (RoundingMode × Int) :=
  [.RNE, .RTZ, .RTN, .RTP, .RNA].flatMap fun mode =>
    (List.range 1025).map fun n => (mode, (n : Int) - 512)

example : cases.all (fun (mode, n) => check mode n) = true := by decide +kernel

#eval do
  for (mode, n) in cases do
    unless check mode n do
      let label := match mode with
        | .RNE => "RNE" | .RTZ => "RTZ" | .RTN => "RTN" | .RTP => "RTP" | .RNA => "RNA"
      throw (IO.userError s!"integer rounding failed: {label}, numerator={n}, denominator=8")
  IO.println s!"PASS: {cases.length} integer-rounding oracle/idempotence cases"

end IntegerRounding

