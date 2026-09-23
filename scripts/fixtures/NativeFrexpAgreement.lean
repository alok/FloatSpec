import FloatSpec.src.IEEE754.PrimFloat

/-! Runtime agreement between Lean's opaque native `Float.frExp` and the
kernel-visible bit-level `nativeFrExp`.

In Lean 4.34 `Float.frExp` is an opaque constant bound to the C function
`lean_float_frexp`, which calls `frexp` and reports exponent `0` for non-finite
inputs.  The kernel cannot evaluate it, so its result can be postulated but
never proved.  The Flocq correspondence is instead proved for `nativeFrExp`
(`FaithfulPrimFloat.PrimitiveFloat.nativeFrExp_equiv`), and this fixture checks,
by execution only, that the native runtime and `nativeFrExp` agree bit for bit
(NaN payloads quotiented to the canonical NaN) on every encoding class: signed
zero, every subnormal leading-bit position, normal exponent boundaries, the
largest finite values, infinities, quiet and signaling NaNs, and seeded random
words.  For nonzero finite inputs it also checks the C contract independently:
the significand magnitude lies in `[1/2, 1)` and `Float.scaleB` reconstructs
the input exactly.  This is execution evidence, not a kernel proof. -/

namespace FloatSpec.Test.NativeFrexpAgreement

open FaithfulPrimFloat.PrimitiveFloat

/-- Significand bits with NaN payloads canonicalized, and the exponent. -/
private def observe (result : Float × Int) : UInt64 × Int :=
  (if result.1.isNaN then 0x7ff8000000000000 else result.1.toBits, result.2)

private def hex (w : UInt64) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 w.toNat)

private def check (w : UInt64) : IO Unit := do
  let x := Float.ofBits w
  let native := observe x.frExp
  let bits := observe (nativeFrExp x)
  unless native == bits do
    throw (IO.userError s!"Float.frExp/nativeFrExp mismatch at {hex w}: \
      native=({hex native.1}, {native.2}); nativeFrExp=({hex bits.1}, {bits.2})")
  if x.isFinite && x != 0 then
    let (significand, exponent) := nativeFrExp x
    let magnitude := significand.abs
    unless 0.5 ≤ magnitude && magnitude < 1 && significand.scaleB exponent == x do
      throw (IO.userError s!"nativeFrExp violates the frexp contract at {hex w}")

/-- Both signs of every exponent/fraction boundary, every single-bit and
low-mask subnormal, and the extreme finite values. -/
def boundaryWords : List UInt64 := Id.run do
  let mut words : Array UInt64 := #[]
  for sign in [(0 : UInt64), 0x8000000000000000] do
    for exponent in [(0 : UInt64), 1, 2, 1021, 1022, 1023, 1024, 2045, 2046, 2047] do
      for fraction in [(0 : UInt64), 1, 2, 0x0007ffffffffffff, 0x0008000000000000,
          0x000ffffffffffffe, 0x000fffffffffffff] do
        words := words.push (sign ||| (exponent <<< 52) ||| fraction)
    for bit in List.range 52 do
      let power : UInt64 := 1 <<< bit.toUInt64
      words := words.push (sign ||| power)
      words := words.push (sign ||| (power - 1))
      words := words.push (sign ||| (power + 1))
      words := words.push (sign ||| (0x000fffffffffffff >>> bit.toUInt64))
  return words.toList

/-- Check boundary words, then seeded random words and random subnormals. -/
def checkAll : IO Nat := do
  let mut count := 0
  for w in boundaryWords do
    check w
    count := count + 1
  let mut state : UInt64 := 20260922
  for _ in [:100000] do
    state := state * 6364136223846793005 + 1442695040888963407
    check state
    -- The same sign with a random-length subnormal fraction.
    check ((state &&& (0x8000000000000000 : UInt64)) |||
      ((state &&& (0x000fffffffffffff : UInt64)) >>> (state >>> 58)))
    count := count + 2
  return count

#eval do
  let count ← checkAll
  IO.println s!"PASS: {count} Float.frExp/nativeFrExp runtime agreements; seed 20260922."

end FloatSpec.Test.NativeFrexpAgreement
