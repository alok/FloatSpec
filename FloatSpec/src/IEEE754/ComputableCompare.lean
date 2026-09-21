import FloatSpec.src.IEEE754.PrimFloat

/-! Executable comparison of dyadic values, retaining Claude's exponent-alignment backend.

This is a Lean-only value API, not a replacement for Flocq's raw-record comparison.
For example, the payloads 3 times 2^-1 and 6 times 2^-2 have equal values, but the
raw source comparator distinguishes them. The proofs below connect this backend
to an explicit local real-valued specification and to the raw comparator on
canonical proof-carrying inputs. Import this module explicitly for arbitrary
dyadic values; the default source-facing API remains `FaithfulPrimFloat`. -/

set_option linter.coqSource true

namespace FloatSpec.IEEE754.ComputableCompare

open FloatSpec.Core.Defs (FlocqFloat)
open FloatSpec.Core.Float_prop

/-! ### Dyadic payloads -/

/-- Signed integer mantissa denoted by a sign bit and a magnitude. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def signedMantissa (s : Bool) (m : Nat) : Int :=
  if s then -(m : Int) else (m : Int)

/-- Strict order on dyadic payloads `n₁ * beta ^ e₁` vs `n₂ * beta ^ e₂`,
    computed by aligning to the smaller exponent.  Fully computable. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def dyadicLt (beta : Int) (n₁ e₁ n₂ e₂ : Int) : Bool :=
  if e₁ ≤ e₂ then n₁ < n₂ * beta ^ (e₂ - e₁).natAbs
  else n₁ * beta ^ (e₁ - e₂).natAbs < n₂

/-- Equality on dyadic payloads, computed by aligning to the smaller
    exponent.  Fully computable. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def dyadicEq (beta : Int) (n₁ e₁ n₂ e₂ : Int) : Bool :=
  if e₁ ≤ e₂ then n₁ = n₂ * beta ^ (e₂ - e₁).natAbs
  else n₁ * beta ^ (e₁ - e₂).natAbs = n₂

/-! ### Correspondence with `F2R`

`F2R_change_exp` rewrites a float at any smaller exponent; `lt_F2R_iff` and
`eq_F2R` then compare mantissas at the now-common exponent. -/

section Correspondence

variable {beta : Int} [ValidRadix beta]

/-- Realigning the larger-exponent operand preserves its real value. -/
private theorem val_align (n e e' : Int) (he : e' ≤ e) :
    FloatSpec.Core.Defs.F2R (FlocqFloat.mk n e : FlocqFloat beta)
      = FloatSpec.Core.Defs.F2R
          (FlocqFloat.mk (n * beta ^ (e - e').natAbs) e' : FlocqFloat beta) :=
  F2R_change_exp (beta := beta) (f := FlocqFloat.mk n e) (e' := e')
    ValidRadix.valid he

/-- `dyadicLt` decides the real strict order on dyadic payloads. -/
theorem dyadicLt_iff (n₁ e₁ n₂ e₂ : Int) :
    dyadicLt beta n₁ e₁ n₂ e₂ = true
      ↔ FloatSpec.Core.Defs.F2R (FlocqFloat.mk n₁ e₁ : FlocqFloat beta)
          < FloatSpec.Core.Defs.F2R (FlocqFloat.mk n₂ e₂ : FlocqFloat beta) := by
  unfold dyadicLt
  split
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₂ e₂ e₁ h]
      exact lt_F2R_iff (beta := beta) e₁ _ _ ValidRadix.valid
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₁ e₁ e₂ (not_le.mp h).le]
      exact lt_F2R_iff (beta := beta) e₂ _ _ ValidRadix.valid

/-- `dyadicEq` decides real equality of dyadic payloads. -/
theorem dyadicEq_iff (n₁ e₁ n₂ e₂ : Int) :
    dyadicEq beta n₁ e₁ n₂ e₂ = true
      ↔ FloatSpec.Core.Defs.F2R (FlocqFloat.mk n₁ e₁ : FlocqFloat beta)
          = FloatSpec.Core.Defs.F2R (FlocqFloat.mk n₂ e₂ : FlocqFloat beta) := by
  unfold dyadicEq
  split
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₂ e₂ e₁ h]
      exact ⟨fun hm => congrArg
               (fun m => FloatSpec.Core.Defs.F2R (FlocqFloat.mk m e₁ : FlocqFloat beta)) hm,
             fun hr => eq_F2R (beta := beta) e₁ _ _ hr⟩
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₁ e₁ e₂ (not_le.mp h).le]
      exact ⟨fun hm => congrArg
               (fun m => FloatSpec.Core.Defs.F2R (FlocqFloat.mk m e₂ : FlocqFloat beta)) hm,
             fun hr => eq_F2R (beta := beta) e₂ _ _ hr⟩

end Correspondence

/-! ### Computable `StandardFloat` comparisons

The local specification below preserves the value interpretation used by the
original comparison backend. It deliberately does not define the raw source API. -/

namespace ValueSpec

open Classical

/-- Equality of represented values, with IEEE exceptional-value conventions. -/
@[flocq_local "Real-valued comparison specification; not Flocq raw SFeqb"]
noncomputable def SFeqb (x y : StandardFloat) : Bool :=
  match x, y with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => sx == sy
  | StandardFloat.S754_infinity _, _ => false
  | _, StandardFloat.S754_infinity _ => false
  | x, y => decide (SF2R 2 x = SF2R 2 y)

/-- Strict order of represented values, handling infinities before mapping to reals. -/
@[flocq_local "Real-valued comparison specification; not Flocq raw SFltb"]
noncomputable def SFltb (x y : StandardFloat) : Bool :=
  match x, y with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => sx && !sy
  | StandardFloat.S754_infinity sx, _ => sx
  | _, StandardFloat.S754_infinity sy => !sy
  | x, y => decide (SF2R 2 x < SF2R 2 y)

/-- Non-strict value order. -/
@[flocq_local "Real-valued comparison specification; not Flocq raw SFleb"]
noncomputable def SFleb (x y : StandardFloat) : Bool := SFltb x y || SFeqb x y

/-- Three-way value comparison, leaving NaN unordered. -/
@[flocq_local "Real-valued comparison specification; not Flocq raw SFcompare"]
noncomputable def SFcompare (x y : StandardFloat) : Option Ordering :=
  match x, y with
  | StandardFloat.S754_nan, _ => none
  | _, StandardFloat.S754_nan => none
  | x, y =>
      if SFltb x y then some Ordering.lt
      else if SFltb y x then some Ordering.gt
      else some Ordering.eq

end ValueSpec

section StandardFloatBackend

/-- Dyadic payload `(mantissa, exponent)` denoted by a `StandardFloat`.
    Zero, infinity and NaN all denote `0` under `SF2R`, matching `(0, 0)`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def payload : StandardFloat → Int × Int
  | StandardFloat.S754_finite s m e => (signedMantissa s m, e)
  | _ => (0, 0)

/-- `SF2R` factors through `payload`. -/
theorem SF2R_eq_payload (x : StandardFloat) :
    SF2R 2 x
      = FloatSpec.Core.Defs.F2R
          (FlocqFloat.mk (payload x).1 (payload x).2 : FlocqFloat 2) := by
  cases x <;> simp [SF2R, payload, signedMantissa]

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.SFltb`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def SFltbC (x y : StandardFloat) : Bool :=
  match x, y with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => sx && !sy
  | StandardFloat.S754_infinity sx, _ => sx
  | _, StandardFloat.S754_infinity sy => !sy
  | x, y => dyadicLt 2 (payload x).1 (payload x).2 (payload y).1 (payload y).2

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.SFeqb`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def SFeqbC (x y : StandardFloat) : Bool :=
  match x, y with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => sx == sy
  | StandardFloat.S754_infinity _, _ => false
  | _, StandardFloat.S754_infinity _ => false
  | x, y => dyadicEq 2 (payload x).1 (payload x).2 (payload y).1 (payload y).2

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.SFleb`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def SFlebC (x y : StandardFloat) : Bool :=
  SFltbC x y || SFeqbC x y

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.SFcompare`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def SFcompareC (x y : StandardFloat) : Option Ordering :=
  match x, y with
  | StandardFloat.S754_nan, _ => none
  | _, StandardFloat.S754_nan => none
  | x, y =>
      if SFltbC x y then some Ordering.lt
      else if SFltbC y x then some Ordering.gt
      else some Ordering.eq

/-- The executable strict order agrees with the local value specification. -/
@[simp] theorem SFltbC_eq_value (x y : StandardFloat) :
    SFltbC x y = ValueSpec.SFltb x y := by
  cases x <;> cases y <;>
    simp only [SFltbC, ValueSpec.SFltb] <;>
    rw [Bool.eq_iff_iff, dyadicLt_iff, decide_eq_true_eq,
        SF2R_eq_payload, SF2R_eq_payload]

/-- The executable equality test agrees with the local value specification. -/
@[simp] theorem SFeqbC_eq_value (x y : StandardFloat) :
    SFeqbC x y = ValueSpec.SFeqb x y := by
  cases x <;> cases y <;>
    simp only [SFeqbC, ValueSpec.SFeqb] <;>
    rw [Bool.eq_iff_iff, dyadicEq_iff, decide_eq_true_eq,
        SF2R_eq_payload, SF2R_eq_payload]

/-- The executable non-strict order agrees with the local value specification. -/
@[simp] theorem SFlebC_eq_value (x y : StandardFloat) :
    SFlebC x y = ValueSpec.SFleb x y := by
  simp [SFlebC, ValueSpec.SFleb]

/-- The executable three-way comparison agrees with the local value specification. -/
@[simp] theorem SFcompareC_eq_value (x y : StandardFloat) :
    SFcompareC x y = ValueSpec.SFcompare x y := by
  cases x <;> cases y <;> simp [SFcompareC, ValueSpec.SFcompare]

end StandardFloatBackend

/-! ### Canonical bridge to the raw source comparator

The finite constructors of `BinarySingleNaNFloat` carry positive-mantissa and
format-bound proofs. Those hypotheses are part of the input type, not optional
side conditions. The theorem also covers signed zero, infinities and NaN. -/

private theorem realCompare_as_lt_lt (x y : Real) :
    (if x < y then some Ordering.lt else if y < x then some Ordering.gt else some Ordering.eq) =
      some (BinarySingleNaN.RcompareOrdering x y) := by
  rcases lt_trichotomy x y with h | h | h
  · simp [BinarySingleNaN.RcompareOrdering, h]
  · subst y; simp [BinarySingleNaN.RcompareOrdering]
  · simp [BinarySingleNaN.RcompareOrdering, h, not_lt_of_ge h.le, ne_of_gt h]

/-- Value and raw comparison agree on canonical inputs of the same format. -/
theorem SFcompareC_eq_raw_of_canonical {prec emax : Int}
    (x y : BinarySingleNaNFloat prec emax) :
    SFcompareC (binarySingleNaNFloatToStandardFloat x) (binarySingleNaNFloatToStandardFloat y) =
      FaithfulPrimFloat.SFcompare (binarySingleNaNFloatToStandardFloat x)
        (binarySingleNaNFloatToStandardFloat y) := by
  rw [SFcompareC_eq_value, FaithfulPrimFloat.SFcompare_B2SF]
  by_cases hx : BinarySingleNaN.is_finite x = true
  · by_cases hy : BinarySingleNaN.is_finite y = true
    · rw [BinarySingleNaN.Bcompare_correct x y hx hy]
      have h := realCompare_as_lt_lt (BinarySingleNaN.B2R x) (BinarySingleNaN.B2R y)
      cases x <;> cases y <;>
        simp_all [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754, BSN_is_finite,
          binarySingleNaNFloatToStandardFloat, ValueSpec.SFcompare, ValueSpec.SFltb,
          BinarySingleNaN.B2R, B754_to_R, SF2R, F2R, FloatSpec.Core.Defs.F2R]
    · cases x <;> cases y <;>
        simp_all [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754, BSN_is_finite,
          binarySingleNaNFloatToStandardFloat, ValueSpec.SFcompare, ValueSpec.SFltb,
          BinarySingleNaN.Bcompare] <;> split_ifs <;> simp_all
  · cases x <;> cases y <;>
      simp_all [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754, BSN_is_finite,
        binarySingleNaNFloatToStandardFloat, ValueSpec.SFcompare, ValueSpec.SFltb,
        BinarySingleNaN.Bcompare] <;> split_ifs <;> simp_all

private theorem ValueSpec.tests_of_compare (x y : StandardFloat) :
    (ValueSpec.SFltb x y, ValueSpec.SFeqb x y, ValueSpec.SFleb x y) =
      (match ValueSpec.SFcompare x y with | some .lt => true | _ => false,
       match ValueSpec.SFcompare x y with | some .eq => true | _ => false,
       match ValueSpec.SFcompare x y with | some .lt | some .eq => true | _ => false) := by
  cases x <;> cases y <;>
    simp only [ValueSpec.SFleb, ValueSpec.SFcompare, ValueSpec.SFltb, ValueSpec.SFeqb]
  all_goals (try split_ifs) <;> simp_all <;> grind

/-- Value and raw strict order agree on canonical inputs of the same format. -/
theorem SFltbC_eq_raw_of_canonical {prec emax : Int}
    (x y : BinarySingleNaNFloat prec emax) :
    SFltbC (binarySingleNaNFloatToStandardFloat x) (binarySingleNaNFloatToStandardFloat y) =
      FaithfulPrimFloat.SFltb (binarySingleNaNFloatToStandardFloat x)
        (binarySingleNaNFloatToStandardFloat y) := by
  have h := ValueSpec.tests_of_compare
    (binarySingleNaNFloatToStandardFloat x) (binarySingleNaNFloatToStandardFloat y)
  rw [← SFcompareC_eq_value, SFcompareC_eq_raw_of_canonical] at h
  rw [SFltbC_eq_value]
  exact (congrArg Prod.fst h : _)

/-- Value and raw equality agree on canonical inputs of the same format. -/
theorem SFeqbC_eq_raw_of_canonical {prec emax : Int}
    (x y : BinarySingleNaNFloat prec emax) :
    SFeqbC (binarySingleNaNFloatToStandardFloat x) (binarySingleNaNFloatToStandardFloat y) =
      FaithfulPrimFloat.SFeqb (binarySingleNaNFloatToStandardFloat x)
        (binarySingleNaNFloatToStandardFloat y) := by
  have h := ValueSpec.tests_of_compare
    (binarySingleNaNFloatToStandardFloat x) (binarySingleNaNFloatToStandardFloat y)
  rw [← SFcompareC_eq_value, SFcompareC_eq_raw_of_canonical] at h
  rw [SFeqbC_eq_value]
  exact (congrArg (fun p => p.2.1) h : _)

/-- Value and raw non-strict order agree on canonical inputs of the same format. -/
theorem SFlebC_eq_raw_of_canonical {prec emax : Int}
    (x y : BinarySingleNaNFloat prec emax) :
    SFlebC (binarySingleNaNFloatToStandardFloat x) (binarySingleNaNFloatToStandardFloat y) =
      FaithfulPrimFloat.SFleb (binarySingleNaNFloatToStandardFloat x)
        (binarySingleNaNFloatToStandardFloat y) := by
  have h := ValueSpec.tests_of_compare
    (binarySingleNaNFloatToStandardFloat x) (binarySingleNaNFloatToStandardFloat y)
  rw [← SFcompareC_eq_value, SFcompareC_eq_raw_of_canonical] at h
  rw [SFlebC_eq_value]
  exact (congrArg (fun p => p.2.2) h : _)

/-! ### Derived layers

`eqb`/`ltb`/`leb`/`compare` on `PrimitiveFloat` and `Beqb`/`Bltb`/`Bleb`/
`Bcompare` on `PrimBinaryFloat` are thin wrappers over the `StandardFloat`
comparisons composed with the *already computable* projections `Prim2SF` and
`B2SF`. These wrappers expose value comparisons, with correctness against
`ValueSpec` inherited from the theorems above. They do not redefine the raw
source-facing wrappers. -/

section DerivedLayers

open FaithfulPrimFloat

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.eqb`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def eqbC (x y : PrimitiveFloat) : Bool := SFeqbC (Prim2SF x) (Prim2SF y)

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.ltb`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def ltbC (x y : PrimitiveFloat) : Bool := SFltbC (Prim2SF x) (Prim2SF y)

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.leb`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def lebC (x y : PrimitiveFloat) : Bool := SFlebC (Prim2SF x) (Prim2SF y)

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.compare`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def compareC (x y : PrimitiveFloat) : float_comparison :=
  flatten_cmp_opt (SFcompareC (Prim2SF x) (Prim2SF y))

/-- The wrapper agrees with dyadic-value comparison, not unrestricted raw-record comparison. -/
@[simp] theorem eqbC_eq_value (x y : PrimitiveFloat) :
    eqbC x y = ValueSpec.SFeqb (Prim2SF x) (Prim2SF y) := by
  simp only [eqbC, SFeqbC_eq_value]

/-- The wrapper agrees with dyadic-value comparison, not unrestricted raw-record comparison. -/
@[simp] theorem ltbC_eq_value (x y : PrimitiveFloat) :
    ltbC x y = ValueSpec.SFltb (Prim2SF x) (Prim2SF y) := by
  simp only [ltbC, SFltbC_eq_value]

/-- The wrapper agrees with dyadic-value comparison, not unrestricted raw-record comparison. -/
@[simp] theorem lebC_eq_value (x y : PrimitiveFloat) :
    lebC x y = ValueSpec.SFleb (Prim2SF x) (Prim2SF y) := by
  simp only [lebC, SFlebC_eq_value]

/-- The wrapper agrees with dyadic-value comparison, not unrestricted raw-record comparison. -/
@[simp] theorem compareC_eq_value (x y : PrimitiveFloat) :
    compareC x y = flatten_cmp_opt (ValueSpec.SFcompare (Prim2SF x) (Prim2SF y)) := by
  simp only [compareC, SFcompareC_eq_value]

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.Beqb`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def BeqbC (x y : PrimBinaryFloat) : Bool := SFeqbC (B2SF x) (B2SF y)

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.Bltb`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def BltbC (x y : PrimBinaryFloat) : Bool := SFltbC (B2SF x) (B2SF y)

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.Bleb`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def BlebC (x y : PrimBinaryFloat) : Bool := SFlebC (B2SF x) (B2SF y)

/-- Dyadic-value alternative to raw `FaithfulPrimFloat.Bcompare`. -/
@[flocq_local "Executable dyadic-value helper; not an unrestricted Flocq raw-record API"]
def BcompareC (x y : PrimBinaryFloat) : Option Ordering :=
  SFcompareC (B2SF x) (B2SF y)

/-- The wrapper agrees with dyadic-value comparison, not unrestricted raw-record comparison. -/
@[simp] theorem BeqbC_eq_value (x y : PrimBinaryFloat) :
    BeqbC x y = ValueSpec.SFeqb (B2SF x) (B2SF y) := by
  simp only [BeqbC, SFeqbC_eq_value]

/-- The wrapper agrees with dyadic-value comparison, not unrestricted raw-record comparison. -/
@[simp] theorem BltbC_eq_value (x y : PrimBinaryFloat) :
    BltbC x y = ValueSpec.SFltb (B2SF x) (B2SF y) := by
  simp only [BltbC, SFltbC_eq_value]

/-- The wrapper agrees with dyadic-value comparison, not unrestricted raw-record comparison. -/
@[simp] theorem BlebC_eq_value (x y : PrimBinaryFloat) :
    BlebC x y = ValueSpec.SFleb (B2SF x) (B2SF y) := by
  simp only [BlebC, SFlebC_eq_value]

/-- The wrapper agrees with dyadic-value comparison, not unrestricted raw-record comparison. -/
@[simp] theorem BcompareC_eq_value (x y : PrimBinaryFloat) :
    BcompareC x y = ValueSpec.SFcompare (B2SF x) (B2SF y) := by
  simp only [BcompareC, SFcompareC_eq_value]

/-- The proof-carrying wrapper supplies the canonical hypotheses for raw comparison. -/
theorem BeqbC_eq_raw (x y : PrimBinaryFloat) : BeqbC x y = FaithfulPrimFloat.Beqb x y := by
  exact SFeqbC_eq_raw_of_canonical x y

/-- The proof-carrying wrapper supplies the canonical hypotheses for raw comparison. -/
theorem eqbC_eq_raw (x y : PrimitiveFloat) : eqbC x y = FaithfulPrimFloat.eqb x y := by
  change SFeqbC (Prim2SF x) (Prim2SF y) = FaithfulPrimFloat.SFeqb (Prim2SF x) (Prim2SF y)
  rw [← B2SF_Prim2B x, ← B2SF_Prim2B y]
  exact SFeqbC_eq_raw_of_canonical (Prim2B x) (Prim2B y)

/-- The proof-carrying wrapper supplies the canonical hypotheses for raw comparison. -/
theorem BltbC_eq_raw (x y : PrimBinaryFloat) : BltbC x y = FaithfulPrimFloat.Bltb x y := by
  exact SFltbC_eq_raw_of_canonical x y

/-- The proof-carrying wrapper supplies the canonical hypotheses for raw comparison. -/
theorem ltbC_eq_raw (x y : PrimitiveFloat) : ltbC x y = FaithfulPrimFloat.ltb x y := by
  change SFltbC (Prim2SF x) (Prim2SF y) = FaithfulPrimFloat.SFltb (Prim2SF x) (Prim2SF y)
  rw [← B2SF_Prim2B x, ← B2SF_Prim2B y]
  exact SFltbC_eq_raw_of_canonical (Prim2B x) (Prim2B y)

/-- The proof-carrying wrapper supplies the canonical hypotheses for raw comparison. -/
theorem BlebC_eq_raw (x y : PrimBinaryFloat) : BlebC x y = FaithfulPrimFloat.Bleb x y := by
  exact SFlebC_eq_raw_of_canonical x y

/-- The proof-carrying wrapper supplies the canonical hypotheses for raw comparison. -/
theorem lebC_eq_raw (x y : PrimitiveFloat) : lebC x y = FaithfulPrimFloat.leb x y := by
  change SFlebC (Prim2SF x) (Prim2SF y) = FaithfulPrimFloat.SFleb (Prim2SF x) (Prim2SF y)
  rw [← B2SF_Prim2B x, ← B2SF_Prim2B y]
  exact SFlebC_eq_raw_of_canonical (Prim2B x) (Prim2B y)

/-- The proof-carrying wrapper supplies the canonical hypotheses for raw comparison. -/
theorem BcompareC_eq_raw (x y : PrimBinaryFloat) : BcompareC x y = FaithfulPrimFloat.Bcompare x y := by
  exact SFcompareC_eq_raw_of_canonical x y

/-- The proof-carrying wrapper supplies the canonical hypotheses for raw comparison. -/
theorem compareC_eq_raw (x y : PrimitiveFloat) : compareC x y = FaithfulPrimFloat.compare x y := by
  apply congrArg flatten_cmp_opt
  change SFcompareC (Prim2SF x) (Prim2SF y) = FaithfulPrimFloat.SFcompare (Prim2SF x) (Prim2SF y)
  rw [← B2SF_Prim2B x, ← B2SF_Prim2B y]
  exact SFcompareC_eq_raw_of_canonical (Prim2B x) (Prim2B y)

end DerivedLayers

end FloatSpec.IEEE754.ComputableCompare
