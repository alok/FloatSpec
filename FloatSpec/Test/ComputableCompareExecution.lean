import FloatSpec.src.IEEE754.ComputableCompare

/-! Direct execution of the computable `StandardFloat` comparison backend.

The `*C` variants compare arbitrary dyadic values by aligning exponents over
`Int`. Their `_eq_value` theorems connect them to the local `ValueSpec`, not
the Flocq raw-record comparison. Both APIs are executable and intentionally
differ on noncanonical representations. The boundary examples below preserve
that distinction.

The `decide +kernel` examples below are the point of the module: they only
succeed because the comparison now reduces in the kernel.  The randomized
`IO` check additionally rejects missing *executable* code. -/

namespace FloatSpec.Test.ComputableCompareExecution

open FloatSpec.IEEE754.ComputableCompare

private def fin (s : Bool) (m : Nat) (e : Int) : StandardFloat :=
  StandardFloat.S754_finite s m e

/-! ### Kernel-reducible observations -/

-- 1.5 encoded as 3·2⁻¹ and as 6·2⁻²: equal values, different payloads.
example : SFeqbC (fin false 3 (-1)) (fin false 6 (-2)) = true := by decide +kernel

-- Distinct values at unequal exponents still order correctly.
example : SFltbC (fin false 3 (-1)) (fin false 7 (-2)) = true := by decide +kernel

-- Signs are respected: -1.5 < 1.5.
example : SFltbC (fin true 3 (-1)) (fin false 3 (-1)) = true := by decide +kernel
example : SFltbC (fin false 3 (-1)) (fin true 3 (-1)) = false := by decide +kernel

-- IEEE 754 §5.11: +0 and -0 compare equal.
example : SFeqbC (StandardFloat.S754_zero false) (StandardFloat.S754_zero true) = true := by
  decide +kernel

-- NaN is unordered: never equal (not even to itself) and never less-than.
example : SFeqbC StandardFloat.S754_nan StandardFloat.S754_nan = false := by decide +kernel
example : SFcompareC StandardFloat.S754_nan (fin false 1 0) = none := by decide +kernel

-- Infinities bracket every finite value.
example : SFltbC (fin false 1 1000) (StandardFloat.S754_infinity false) = true := by
  decide +kernel
example : SFltbC (StandardFloat.S754_infinity true) (fin true 1 1000) = true := by
  decide +kernel

-- Three-way comparison agrees with the Boolean tests.
example : SFcompareC (fin true 3 (-1)) (fin false 3 (-1)) = some Ordering.lt := by decide +kernel
example : SFcompareC (fin false 3 (-1)) (fin false 6 (-2)) = some Ordering.eq := by decide +kernel

-- Flocq's raw-record comparator is not arbitrary dyadic-value comparison.
example : FaithfulPrimFloat.SFcompare (fin false 3 (-1)) (fin false 6 (-2)) =
    some Ordering.gt := by decide +kernel

example : FaithfulPrimFloat.SFeqb (fin false 3 (-1)) (fin false 6 (-2)) = false := by
  decide +kernel

/-! ### Randomized invariants

A compiled-only differential grid.  The kernel examples above cannot catch a
definition that reduces but has no compiled code; this check does. -/

def checkInvariants : IO Unit := do
  let mut state : UInt64 := 526913
  for _ in [:20000] do
    state := state * 6364136223846793005 + 1442695040888963407
    let s₁ := (state >>> 3) % 2 == 1
    let m₁ := ((state >>> 7) % 64).toNat
    let e₁ : Int := ((state >>> 13) % 17).toNat - 8
    state := state * 6364136223846793005 + 1442695040888963407
    let s₂ := (state >>> 3) % 2 == 1
    let m₂ := ((state >>> 7) % 64).toNat
    let e₂ : Int := ((state >>> 13) % 17).toNat - 8
    let x := fin s₁ m₁ e₁
    let y := fin s₂ m₂ e₂
    -- Trichotomy: exactly one of <, >, = holds for finite payloads.
    let lt := SFltbC x y
    let gt := SFltbC y x
    let eq := SFeqbC x y
    unless [lt, gt, eq].count true == 1 do
      throw (IO.userError s!"trichotomy failed: {m₁}·2^{e₁} vs {m₂}·2^{e₂}")
    -- Reflexivity on finite payloads.
    unless SFeqbC x x do
      throw (IO.userError s!"reflexivity failed: {m₁}·2^{e₁}")
    -- `≤` is exactly `<` or `=`.
    unless SFlebC x y == (lt || eq) do
      throw (IO.userError s!"leb disagrees: {m₁}·2^{e₁} vs {m₂}·2^{e₂}")
    -- Scaling the payload by the radix leaves the value unchanged.
    unless SFeqbC x (fin s₁ (2 * m₁) (e₁ - 1)) do
      throw (IO.userError s!"radix scaling failed: {m₁}·2^{e₁}")
    -- `SFcompareC` agrees with the Boolean tests.
    let expected := if lt then some Ordering.lt else if gt then some Ordering.gt
                    else some Ordering.eq
    unless SFcompareC x y == expected do
      throw (IO.userError s!"compare disagrees: {m₁}·2^{e₁} vs {m₂}·2^{e₂}")
  IO.println "ComputableCompare: 20000 randomized payload pairs passed"

#eval checkInvariants

/-! ### Canonical inputs: the bridge is a theorem, not an assumed representation law. -/

private theorem canonicalBridge {prec emax : Int} (x y : BinarySingleNaNFloat prec emax) :
    SFcompareC (binarySingleNaNFloatToStandardFloat x) (binarySingleNaNFloatToStandardFloat y) =
      FaithfulPrimFloat.SFcompare (binarySingleNaNFloatToStandardFloat x)
        (binarySingleNaNFloatToStandardFloat y) :=
  SFcompareC_eq_raw_of_canonical x y

#print axioms canonicalBridge
#print axioms eqbC_eq_raw
#print axioms compareC_eq_raw

/-- Run all four canonical comparison bridges on ordinary and degenerate formats. -/
def checkCanonicalBridge : IO Unit := do
  let mut raw : Array StandardFloat := #[.S754_zero false, .S754_zero true,
    .S754_infinity false, .S754_infinity true, .S754_nan]
  for s in [false, true] do
    for m in [1, 3, 7, 8] do
      for e in [-3, 0, 1] do
        raw := raw.push (.S754_finite s m e)
  let mut count := 0
  for (prec, emax) in [(3, 4), (1, 2), (8, 2), (0, 0)] do
    for a in raw do
      for b in raw do
        -- The conversion rejects invalid encodings as NaN, not by normalizing.
        let x := binarySingleNaNFloatToStandardFloat
          (BinarySingleNaN.SF2B' (prec := prec) (emax := emax) a)
        let y := binarySingleNaNFloatToStandardFloat
          (BinarySingleNaN.SF2B' (prec := prec) (emax := emax) b)
        unless SFcompareC x y == FaithfulPrimFloat.SFcompare x y &&
            SFeqbC x y == FaithfulPrimFloat.SFeqb x y &&
            SFltbC x y == FaithfulPrimFloat.SFltb x y &&
            SFlebC x y == FaithfulPrimFloat.SFleb x y do
          throw (IO.userError s!"canonical bridge failed: format={prec},{emax}, pair={count}")
        count := count + 1
  IO.println s!"ComputableCompare: {count} canonical pairs, four comparisons each passed"

#eval checkCanonicalBridge

end FloatSpec.Test.ComputableCompareExecution
