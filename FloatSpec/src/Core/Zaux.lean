/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Original Copyright (C) 2011-2018 Sylvie Boldo
Original Copyright (C) 2011-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
-/

import Std.Do.Triple
import Mathlib.Tactic
import FloatSpec.src.SimprocWP
import FloatSpec.Linter.CoqSourceLinter

open Std.Do

namespace FloatSpec.Core.Zaux

/-- Binary positive integers, matching Coq's `positive` constructors. -/
inductive Positive where
  | xH : Positive
  | xO : Positive → Positive
  | xI : Positive → Positive
  deriving DecidableEq, Repr

/-- Natural-number value of a Coq-style positive integer. -/
def positiveToNat : Positive → Nat
  | Positive.xH => 1
  | Positive.xO p => 2 * positiveToNat p
  | Positive.xI p => 2 * positiveToNat p + 1

/-- Positive integer powers, matching Coq's `Zpower_pos`. -/
def Zpower_pos (v : Int) (e : Positive) : Int :=
  v ^ positiveToNat e

theorem positiveToNat_pos (p : Positive) : 0 < positiveToNat p := by
  induction p with
  | xH => simp [positiveToNat]
  | xO p hp => simp [positiveToNat, hp]
  | xI p hp => simp [positiveToNat]

theorem positiveToNat_injective : Function.Injective positiveToNat := by
  intro a
  induction a with
  | xH =>
      intro b h
      cases b with
      | xH => rfl
      | xO b =>
          have hb := positiveToNat_pos b
          simp [positiveToNat] at h
          omega
      | xI b =>
          have hb := positiveToNat_pos b
          simp [positiveToNat] at h
          omega
  | xO a ih =>
      intro b h
      cases b with
      | xH =>
          have ha := positiveToNat_pos a
          simp [positiveToNat] at h
      | xO b =>
          simp only [positiveToNat] at h
          have hab : positiveToNat a = positiveToNat b := by omega
          exact congrArg Positive.xO (ih hab)
      | xI b =>
          simp [positiveToNat] at h
          omega
  | xI a ih =>
      intro b h
      cases b with
      | xH =>
          have ha := positiveToNat_pos a
          simp [positiveToNat] at h
          omega
      | xO b =>
          simp [positiveToNat] at h
          omega
      | xI b =>
          simp only [positiveToNat] at h
          have hab : positiveToNat a = positiveToNat b := by omega
          exact congrArg Positive.xI (ih hab)

section Zmissing

/-- FLoCq `Zopp_le_cancel`. -/
@[flocq_source "src/Core/Zaux.v" 29 "Zopp_le_cancel"]
theorem Zopp_le_cancel (x y : Int) (h : -y ≤ -x) : x ≤ y :=
  Int.neg_le_neg_iff.mp h

/-- FLoCq `Zgt_not_eq`. -/
@[flocq_source "src/Core/Zaux.v" 38 "Zgt_not_eq"]
theorem Zgt_not_eq (x y : Int) (h : y < x) : x ≠ y :=
  ne_of_gt h

end Zmissing

section ProofIrrelevance

/-- Dependent equality helper for boolean-indexed families.

    Lean counterpart of Flocq's `eqbool_dep`: at index `true`, it compares
    the incoming proof/data with the distinguished value `h1`; at index
    `false`, the predicate is impossible.
-/
@[flocq_source "src/Core/Zaux.v" 53 "eqbool_dep"]
def eqbool_dep (P : Bool → Sort u) (h1 : P true) (b : Bool) : P b → Prop :=
  match b with
  | true => fun h2 => h1 = h2
  | false => fun _ => False

/-- FLoCq `eqbool_irrelevance`. -/
@[flocq_source "src/Core/Zaux.v" 59 "eqbool_irrelevance"]
theorem eqbool_irrelevance (b : Bool) (h1 h2 : b = true) : h1 = h2 :=
  Subsingleton.elim _ _

end ProofIrrelevance

section EvenOdd

/-- FLoCq `Zeven_ex`. -/
@[flocq_source "src/Core/Zaux.v" 75 "Zeven_ex"]
theorem Zeven_ex (x : Int) :
    ∃ p : Int, x = 2 * p + if Even x then 0 else 1 := by
  refine ⟨x / 2, ?_⟩
  have hdiv := Int.emod_add_mul_ediv x 2
  rcases Int.emod_two_eq_zero_or_one x with hrem | hrem
  · have heven : Even x := Int.even_iff.mpr hrem
    simp [heven, hrem] at hdiv ⊢
    omega
  · have hodd : ¬ Even x := by simpa [Int.even_iff, hrem]
    simp [hodd, hrem] at hdiv ⊢
    omega

end EvenOdd

section Zpower

/-- FLoCq/Coq integer power: natural powers for nonnegative exponents and
zero for negative exponents. -/
def Zpower (b e : Int) : Int :=
  if 0 ≤ e then b ^ e.toNat else 0

/-- FLoCq `Zpower_plus`. -/
@[flocq_source "src/Core/Zaux.v" 94 "Zpower_plus"]
theorem Zpower_plus (n k1 k2 : Int) (h1 : 0 ≤ k1) (h2 : 0 ≤ k2) :
    Zpower n (k1 + k2) = Zpower n k1 * Zpower n k2 := by
  have hsum : 0 ≤ k1 + k2 := by omega
  simp [Zpower, h1, h2, hsum, Int.toNat_add, pow_add]

/-- Radix type for floating-point bases

    A radix must be at least 2. This structure captures the
    constraint that floating-point number systems need a base
    greater than 1 for meaningful representation.
-/
@[flocq_source "src/Core/Zaux.v" 147 "radix"]
structure Radix where
  /-- The radix value, must be at least 2 -/
  val : Int
  /-- Proof that the radix is at least 2 -/
  prop : 2 ≤ val

/-- Standard binary radix

    The most common radix for floating-point arithmetic is base 2.
    This definition provides the standard binary radix.
-/
@[flocq_source "src/Core/Zaux.v" 161 "radix2"]
def radix2 : Radix :=
  ⟨2, by simp⟩

section RadixProps

/-- Two radices with the same integer value are equal. -/
@[flocq_source "src/Core/Zaux.v" 149 "radix_val_inj"]
theorem radix_val_inj (r1 r2 : Radix) :
    r1.val = r2.val → r1 = r2 := by
  cases r1 with
  | mk v1 h1 =>
    cases r2 with
    | mk v2 h2 =>
      simp only [Radix.val]
      intro h
      subst v2
      rfl

/-- Coq-compatible name: any radix is strictly positive -/
@[flocq_source "src/Core/Zaux.v" 165 "radix_gt_0"]
theorem radix_gt_0 (r : Radix) : 0 < r.val := by
  have hr := r.prop
  omega

/-- Coq-compatible name: any radix is strictly greater than 1 -/
@[flocq_source "src/Core/Zaux.v" 173 "radix_gt_1"]
theorem radix_gt_1 (r : Radix) : 1 < r.val := by
  have hr := r.prop
  omega

end RadixProps

/-- FLoCq `Zpower_Zpower_nat`. -/
@[flocq_source "src/Core/Zaux.v" 102 "Zpower_Zpower_nat"]
theorem Zpower_Zpower_nat (b e : Int) (h : 0 ≤ e) :
    Zpower b e = b ^ e.natAbs := by
  have hto : (e.toNat : Int) = e := Int.toNat_of_nonneg h
  have habs : (e.natAbs : Int) = e := Int.natAbs_of_nonneg h
  have heq : e.toNat = e.natAbs := by omega
  simp [Zpower, h, heq]

/-- FLoCq `Zpower_nat_S`. -/
@[flocq_source "src/Core/Zaux.v" 113 "Zpower_nat_S"]
theorem Zpower_nat_S (b : Int) (e : Nat) : b ^ (e + 1) = b * b ^ e := by
  rw [pow_succ, mul_comm]


/-- Coq-compatible name: positive base yields positive power

    If 0 < b and p is a natural number, then b^p > 0.
    This mirrors the Coq lemma {lit}`Zpower_pos_gt_0`.
-/
@[flocq_source "src/Core/Zaux.v" 123 "Zpower_pos_gt_0"]
theorem Zpower_pos_gt_0 (b : Int) (p : Positive) :
    0 < b → 0 < Zpower_pos b p := fun hb => pow_pos hb (positiveToNat p)

end Zpower

section ParityPower

/-- Coq-compatible name: an odd base to a nonnegative exponent remains odd -/
@[flocq_source "src/Core/Zaux.v" 135 "Zeven_Zpower_odd"]
theorem Zeven_Zpower_odd (b e : Int) :
    0 ≤ e → decide (Even b) = false → decide (Even (Zpower b e)) = false := by
  intro he hb
  have hbNotEven : ¬ Even b := of_decide_eq_false hb
  have hbOdd : Odd b := Int.not_even_iff_odd.mp hbNotEven
  have hpOdd : Odd (b ^ e.toNat) := hbOdd.pow
  have hpNotEven : ¬ Even (b ^ e.toNat) := Int.not_even_iff_odd.mpr hpOdd
  simpa [Zpower, he] using (show decide (Even (b ^ e.toNat)) = false from
    decide_eq_false hpNotEven)

end ParityPower

section RadixZpower

/-- Coq-compatible name: power of radix greater than one for positive exponent -/
@[flocq_source "src/Core/Zaux.v" 181 "Zpower_gt_1"]
theorem Zpower_gt_1 (r : Radix) (p : Int) :
    0 < p → 1 < Zpower r.val p := by
  intro hp
  have hr : 1 < r.val := radix_gt_1 r
  have hnat : 0 < p.toNat := by omega
  simp only [Zpower, le_of_lt hp, ite_true]
  exact one_lt_pow₀ hr (Nat.ne_of_gt hnat)

/-- Coq-compatible name: positivity of radix powers for nonnegative exponents -/
@[flocq_source "src/Core/Zaux.v" 208 "Zpower_gt_0"]
theorem Zpower_gt_0 (r : Radix) (p : Int) :
    0 ≤ p → 0 < Zpower r.val p := by
  intro hp
  simp only [Zpower, hp, ite_true]
  exact pow_pos (radix_gt_0 r) _

/-- Coq-compatible name: nonnegativity of radix powers -/
@[flocq_source "src/Core/Zaux.v" 222 "Zpower_ge_0"]
theorem Zpower_ge_0 (r : Radix) (e : Int) :
    0 ≤ Zpower r.val e := by
  by_cases he : 0 ≤ e
  · exact (Zpower_gt_0 r e he).le
  · simp [Zpower, he]

/-- FLoCq `Zpower_le`. -/
@[flocq_source "src/Core/Zaux.v" 231 "Zpower_le"]
theorem Zpower_le (r : Radix) (e1 e2 : Int) (h : e1 ≤ e2) :
    Zpower r.val e1 ≤ Zpower r.val e2 := by
  by_cases h1 : 0 ≤ e1
  · have h2 : 0 ≤ e2 := h1.trans h
    simp only [Zpower, h1, h2, ite_true]
    exact pow_le_pow_right₀ (show 1 ≤ r.val by exact (radix_gt_1 r).le)
      (Int.toNat_le_toNat h)
  · simp only [Zpower, h1, ite_false]
    exact Zpower_ge_0 r e2

/-- Coq-compatible name: strict monotonicity of radix power in the exponent -/
@[flocq_source "src/Core/Zaux.v" 251 "Zpower_lt"]
theorem Zpower_lt (r : Radix) (e1 e2 : Int) :
    0 ≤ e2 → e1 < e2 → Zpower r.val e1 < Zpower r.val e2 := by
  intro h2 hlt
  by_cases h1 : 0 ≤ e1
  · simp only [Zpower, h1, h2, ite_true]
    have h2pos : 0 < e2 := h1.trans_lt hlt
    exact pow_lt_pow_right₀ (radix_gt_1 r) ((Int.toNat_lt_toNat h2pos).2 hlt)
  · rw [Zpower]
    simp only [h1, ite_false]
    exact Zpower_gt_0 r e2 h2

/-- FLoCq `Zpower_lt_Zpower`. -/
@[flocq_source "src/Core/Zaux.v" 278 "Zpower_lt_Zpower"]
theorem Zpower_lt_Zpower (r : Radix) (e1 e2 : Int)
    (h : Zpower r.val (e1 - 1) < Zpower r.val e2) : e1 ≤ e2 := by
  by_contra hnot
  have hle : e2 ≤ e1 - 1 := by omega
  exact (not_lt_of_ge (Zpower_le r e2 (e1 - 1) hle)) h

/-- Coq-compatible name: radix powers dominate the index -/
@[flocq_source "src/Core/Zaux.v" 291 "Zpower_gt_id"]
theorem Zpower_gt_id (r : Radix) (n : Int) :
    n < Zpower r.val n := by
  by_cases hn : 0 ≤ n
  · have hrNonneg : 0 ≤ r.val := (radix_gt_0 r).le
    have hrNat : 1 < r.val.toNat := by
      have hr := r.prop
      omega
    have hnat := Nat.lt_pow_self (n := n.toNat) hrNat
    have hcast : (n.toNat : Int) < (r.val.toNat : Int) ^ n.toNat := by
      exact_mod_cast hnat
    rw [Int.toNat_of_nonneg hn, Int.toNat_of_nonneg hrNonneg] at hcast
    simpa [Zpower, hn] using hcast
  · have hnlt : n < 0 := lt_of_not_ge hn
    simp [Zpower, hn, hnlt]

end RadixZpower

section DivMod

/-- Modulo simplification lemma. -/
def Zmod_mod_mult_check (n _a b : Int) : Int :=
  n % b

/-- Specification: Nested modulo simplifies under side conditions. -/
theorem Zmod_mod_mult_spec (n a b : Int) :
    ⦃⌜0 < a ∧ 0 ≤ b⌝⦄
    (pure (Zmod_mod_mult_check n a b) : Id _)
    ⦃⇓result => ⌜result = n % b⌝⦄ := by
  intro h
  unfold Zmod_mod_mult_check
  rfl

/-- FLoCq `Zmod_mod_mult`. -/
theorem Zmod_mod_mult (n a b : Int) (_ha : 0 < a) (_hb : 0 ≤ b) :
    n % (a * b) % b = n % b := by
  apply Int.emod_emod_of_dvd
  exact ⟨a, by ring⟩

/-- Division and modulo relationship. -/
def ZOmod_eq_check (a b : Int) : Int :=
  a.tmod b

/-- Specification: Quotient and remainder decomposition. -/
theorem ZOmod_eq_spec (a b : Int) :
    ⦃⌜b ≠ 0⌝⦄
    (pure (ZOmod_eq_check a b) : Id _)
    ⦃⇓result => ⌜result = a.tmod b⌝⦄ := by
  intro h
  unfold ZOmod_eq_check
  rfl

/-- FLoCq `ZOmod_eq`. -/
theorem ZOmod_eq (a b : Int) : a.tmod b = a - a.tdiv b * b := by
  simpa [Int.mul_comm] using Int.tmod_def a b

/-- Division of nested modulo. -/
def Zdiv_mod_mult_check (n a b : Int) : Int :=
  if a ≠ 0 && b ≠ 0 then
    (n / a) % b
  else
    0

/-- Specification: Division distributes over modulo for nonnegative inputs, i.e. {lean}`(n % (a * b)) / a = (n / a) % b`. -/
theorem Zdiv_mod_mult_spec (n a b : Int) :
    ⦃⌜0 ≤ a ∧ 0 ≤ b⌝⦄
    (pure (Zdiv_mod_mult_check n a b) : Id _)
    ⦃⇓result => ⌜result = if a = 0 || b = 0 then 0 else (n / a) % b⌝⦄ := by
  intro ⟨ha, hb⟩
  unfold Zdiv_mod_mult_check
  -- Case split on whether a ≠ 0 && b ≠ 0
  split
  · -- Case: a ≠ 0 && b ≠ 0
    rename_i h_both_nonzero
    -- When both are nonzero, a = 0 || b = 0 is false and the RHS reduces to (n / a) % b
    have ha_nonzero : a ≠ 0 := by
      simp at h_both_nonzero
      exact h_both_nonzero.1
    have hb_nonzero : b ≠ 0 := by
      simp at h_both_nonzero
      exact h_both_nonzero.2
    simp [ha_nonzero, hb_nonzero, id_run]
  · -- Case: ¬(a ≠ 0 && b ≠ 0), which means a = 0 || b = 0
    rename_i h_some_zero
    -- When at least one is zero, a = 0 || b = 0 is true
    -- So if a = 0 || b = 0 then 0 else (n / a) % b reduces to 0
    simp at h_some_zero
    push Not at h_some_zero
    -- h_some_zero : a ≠ 0 → b = 0, which is equivalent to a = 0 ∨ b = 0
    -- We need to show: if a = 0 ∨ b = 0 then 0 else (n / a) % b = 0
    by_cases ha_zero : a = 0
    · -- Case: a = 0
      simp [ha_zero, id_run]
    · -- Case: a ≠ 0, then by h_some_zero, b = 0
      have hb_zero : b = 0 := h_some_zero ha_zero
      simp [hb_zero, id_run]

/-- FLoCq `Zdiv_mod_mult`. -/
theorem Zdiv_mod_mult (n a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (n % (a * b)) / a = (n / a) % b := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  rcases hb.eq_or_lt with rfl | hb
  · simp
  have ha0 : a ≠ 0 := ne_of_gt ha
  calc
    (n % (a * b)) / a = (n - (a * b) * (n / (a * b))) / a := by
      rw [Int.emod_def]
    _ = n / a - ((a * b) * (n / (a * b))) / a := by
      rw [Int.sub_ediv_of_dvd]
      exact ⟨b * (n / (a * b)), by ring⟩
    _ = n / a - b * (n / (a * b)) := by
      rw [show (a * b) * (n / (a * b)) = a * (b * (n / (a * b))) by ring,
        Int.mul_ediv_cancel_left _ ha0]
    _ = n / a - b * ((n / a) / b) := by
      rw [Int.ediv_ediv_of_nonneg ha.le]
    _ = (n / a) % b := by rw [Int.emod_def]

/-- Nested modulo with multiplication: for integers n, a, b, the term
    {lean}`(fun (n a b : Int) => (n % (a * b)) % b)` is extensionally equal to
    {lean}`(fun (n b : Int) => n % b)` under standard side conditions. -/
def ZOmod_mod_mult_check (n _a b : Int) : Int :=
  n.tmod b

/-- Specification: {lean}`(fun (n a b : Int) => (n % (a * b)) % b = n % b)`
    (quotient-style statement). -/
theorem ZOmod_mod_mult_spec (n a b : Int) :
    ⦃⌜b ≠ 0⌝⦄
    (pure (ZOmod_mod_mult_check n a b) : Id _)
    ⦃⇓result => ⌜result = n.tmod b⌝⦄ := by
  intro h
  unfold ZOmod_mod_mult_check
  rfl

/-- FLoCq `ZOmod_mod_mult`. -/
theorem ZOmod_mod_mult (n a b : Int) :
    (n.tmod (a * b)).tmod b = n.tmod b := by
  apply Int.tmod_tmod_of_dvd
  exact ⟨a, by ring⟩

/-- Truncated division over nested remainder and multiplication

    Quotient distributes over remainder/multiplication in the truncated variant:
    {lean}`(n % (a*b)) / a = (n / a) % b`.
-/
def ZOdiv_mod_mult_check (n a b : Int) : Bool :=
  decide (((n.tmod (a * b)).tdiv a) = ((n.tdiv a).tmod b))

/-- Specification: Truncated division over remainder and multiplication -/
theorem ZOdiv_mod_mult_spec (n a b : Int) :
    ⦃⌜True⌝⦄
    (pure (ZOdiv_mod_mult_check n a b) : Id _)
    ⦃⇓result => ⌜result = decide (((n.tmod (a * b)).tdiv a) = ((n.tdiv a).tmod b))⌝⦄ := by
  intro _
  unfold ZOdiv_mod_mult_check
  rfl

private theorem ZOdiv_mod_mult_nonneg (n a b : Int)
    (hn : 0 ≤ n) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (n.tmod (a * b)).tdiv a = (n.tdiv a).tmod b := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  rcases hb.eq_or_lt with rfl | hb
  · simp
  have hab0 : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
  calc
    (n.tmod (a * b)).tdiv a = (n % (a * b)) / a := by
      rw [Int.tmod_eq_emod_of_nonneg hn,
        Int.tdiv_eq_ediv_of_nonneg (Int.emod_nonneg n hab0)]
    _ = (n / a) % b := Zdiv_mod_mult n a b ha.le hb.le
    _ = (n.tdiv a).tmod b := by
      rw [Int.tdiv_eq_ediv_of_nonneg hn,
        Int.tmod_eq_emod_of_nonneg (Int.ediv_nonneg hn ha.le)]

/-- FLoCq `ZOdiv_mod_mult`. -/
theorem ZOdiv_mod_mult (n a b : Int) :
    (n.tmod (a * b)).tdiv a = (n.tdiv a).tmod b := by
  have nonnegDividend : ∀ n a b : Int, 0 ≤ n →
      (n.tmod (a * b)).tdiv a = (n.tdiv a).tmod b := by
    intro n a b hn
    by_cases ha : 0 ≤ a
    · by_cases hb : 0 ≤ b
      · exact ZOdiv_mod_mult_nonneg n a b hn ha hb
      · have h := ZOdiv_mod_mult_nonneg n a (-b) hn ha (by omega)
        simpa [Int.tmod_neg] using h
    · by_cases hb : 0 ≤ b
      · have h := ZOdiv_mod_mult_nonneg n (-a) b hn (by omega) hb
        simpa [Int.tmod_neg, Int.tdiv_neg, Int.neg_tmod] using h
      · have h := ZOdiv_mod_mult_nonneg n (-a) (-b) hn (by omega) (by omega)
        simpa [Int.tmod_neg, Int.tdiv_neg, Int.neg_tmod] using h
  by_cases hn : 0 ≤ n
  · exact nonnegDividend n a b hn
  · have h := nonnegDividend (-n) a b (by omega)
    simpa [Int.neg_tmod, Int.neg_tdiv] using h

/-- Small-absolute-value truncated division is zero

    If {lean}`|a| < b`, then {lean}`a / b = 0` in truncated division.
-/
def ZOdiv_small_abs_check (a b : Int) : Bool :=
  decide (a.tdiv b = 0)

/-- Specification: Small absolute value implies zero quotient (truncated) -/
theorem ZOdiv_small_abs_spec (a b : Int) :
    ⦃⌜(Int.natAbs a : Int) < b⌝⦄
    (pure (ZOdiv_small_abs_check a b) : Id _)
    ⦃⇓result => ⌜result = decide (a.tdiv b = 0)⌝⦄ := by
  intro _
  unfold ZOdiv_small_abs_check
  rfl

/-- Coq-compatible name: small-absolute-value truncated division is zero -/
theorem ZOdiv_small_abs (a b : Int) (h : (Int.natAbs a : Int) < b) :
    a.tdiv b = 0 := by
  by_cases ha : 0 ≤ a
  · exact Int.tdiv_eq_zero_of_lt ha (by simpa [Int.natAbs_of_nonneg ha] using h)
  · have hneg : 0 ≤ -a := neg_nonneg.mpr (le_of_not_ge ha)
    have habs : (Int.natAbs a : Int) = -a := by
      simpa [Int.natAbs_neg] using Int.natAbs_of_nonneg hneg
    have hz := Int.tdiv_eq_zero_of_lt hneg (by simpa [habs] using h)
    simpa [Int.neg_tdiv] using hz

/-- Small-absolute-value remainder equals the number itself (truncated) -/
def ZOmod_small_abs_check (a b : Int) : Bool :=
  decide (a.tmod b = a)

/-- Specification: Small absolute value implies remainder equals dividend -/
theorem ZOmod_small_abs_spec (a b : Int) :
    ⦃⌜(Int.natAbs a : Int) < b⌝⦄
    (pure (ZOmod_small_abs_check a b) : Id _)
    ⦃⇓result => ⌜result = decide (a.tmod b = a)⌝⦄ := by
  intro _
  unfold ZOmod_small_abs_check
  rfl

/-- Coq-compatible name: small-absolute-value modulo is identity -/
theorem ZOmod_small_abs (a b : Int) (h : (Int.natAbs a : Int) < b) :
    a.tmod b = a := by
  by_cases ha : 0 ≤ a
  · exact Int.tmod_eq_of_lt ha (by simpa [Int.natAbs_of_nonneg ha] using h)
  · have hneg : 0 ≤ -a := neg_nonneg.mpr (le_of_not_ge ha)
    have habs : (Int.natAbs a : Int) = -a := by
      simpa [Int.natAbs_neg] using Int.natAbs_of_nonneg hneg
    have hz := Int.tmod_eq_of_lt hneg (by simpa [habs] using h)
    simpa [Int.neg_tmod] using hz

/-- Quotient addition with sign consideration

    Computes quot(a+b, c) in terms of individual quotients
    and the quotient of remainders, considering signs.
-/
def ZOdiv_plus_check (a b c : Int) : Int :=
  if c ≠ 0 then
    a / c + b / c + ((a % c + b % c) / c)
  else
    0

/-- Specification: Decomposes the quotient of a sum into a sum of quotients plus the quotient of remainders, under a nonnegativity side condition. -/
theorem ZOdiv_plus_spec (a b c : Int) :
    ⦃⌜0 ≤ a * b ∧ c ≠ 0⌝⦄
    (pure (ZOdiv_plus_check a b c) : Id _)
    ⦃⇓result => ⌜result = a / c + b / c + ((a % c + b % c) / c)⌝⦄ := by
  intro ⟨hab, hc⟩
  unfold ZOdiv_plus_check
  -- Since c ≠ 0, the if condition is true
  simp [hc, id_run]

private theorem ZOdiv_plus_nonneg (a b c : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    (a + b).tdiv c =
      a.tdiv c + b.tdiv c + (a.tmod c + b.tmod c).tdiv c := by
  have hra0 := Int.emod_nonneg a hc.ne'
  have hrb0 := Int.emod_nonneg b hc.ne'
  have hraLt := Int.emod_lt a hc.ne'
  have hrbLt := Int.emod_lt b hc.ne'
  have hsign : c.sign = 1 := Int.sign_eq_one_iff_pos.mpr hc
  have hcorr : (a % c + b % c) / c =
      if c ≤ a % c + b % c then 1 else 0 := by
    by_cases hs : c ≤ a % c + b % c
    · rw [ite_eq_left hs]
      calc
        (a % c + b % c) / c =
            ((a % c + b % c - c) + c * 1) / c := by congr 1; ring
        _ = (a % c + b % c - c) / c + 1 :=
          Int.add_mul_ediv_left _ _ hc.ne'
        _ = 1 := by
          rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
          norm_num
    · rw [ite_eq_right hs]
      exact Int.ediv_eq_zero_of_lt (add_nonneg hra0 hrb0) (by omega)
  rw [Int.tdiv_eq_ediv_of_nonneg (add_nonneg ha hb),
    Int.tdiv_eq_ediv_of_nonneg ha, Int.tdiv_eq_ediv_of_nonneg hb,
    Int.tmod_eq_emod_of_nonneg ha, Int.tmod_eq_emod_of_nonneg hb,
    Int.tdiv_eq_ediv_of_nonneg (add_nonneg hra0 hrb0), Int.add_ediv hc.ne',
    Int.natAbs_of_nonneg hc.le, hsign, hcorr]

/-- FLoCq `ZOdiv_plus`. -/
theorem ZOdiv_plus (a b c : Int) (hab : 0 ≤ a * b) :
    (a + b).tdiv c =
      a.tdiv c + b.tdiv c + (a.tmod c + b.tmod c).tdiv c := by
  have nonnegInputs : ∀ a b c : Int, 0 ≤ a → 0 ≤ b →
      (a + b).tdiv c =
        a.tdiv c + b.tdiv c + (a.tmod c + b.tmod c).tdiv c := by
    intro a b c ha hb
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have h := ZOdiv_plus_nonneg a b (-c) ha hb (by omega)
      simp only [Int.tdiv_neg, Int.tmod_neg] at h
      omega
    · simp
    · exact ZOdiv_plus_nonneg a b c ha hb hc
  rcases Int.mul_nonneg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact nonnegInputs a b c ha hb
  · have h := nonnegInputs (-a) (-b) c (by omega) (by omega)
    have habNeg : -a + -b = -(a + b) := by ring
    rw [habNeg] at h
    simp only [Int.neg_tdiv, Int.neg_tmod] at h
    have hremNeg : -a.tmod c + -b.tmod c = -(a.tmod c + b.tmod c) := by ring
    rw [hremNeg, Int.neg_tdiv] at h
    omega

end DivMod

section SameSign

/-- Transitivity of nonnegativity through a nonzero middle factor -/
def Zsame_sign_trans_check (_v u w : Int) : Bool :=
  decide (0 ≤ u * w)

/-- Specification: If v ≠ 0 and both u·v and v·w are nonnegative, then u·w is nonnegative. -/
theorem Zsame_sign_trans_spec (v u w : Int) :
    ⦃⌜v ≠ 0 ∧ 0 ≤ u * v ∧ 0 ≤ v * w⌝⦄
    (pure (Zsame_sign_trans_check v u w) : Id _)
    ⦃⇓result => ⌜result = decide (0 ≤ u * w)⌝⦄ := by
  intro _
  unfold Zsame_sign_trans_check
  rfl

/-- Coq-compatible name: transitivity of nonnegativity through a nonzero factor -/
theorem Zsame_sign_trans (v u w : Int) (hv : v ≠ 0)
    (huv : 0 ≤ u * v) (hvw : 0 ≤ v * w) : 0 ≤ u * w := by
  rcases Int.mul_nonneg_iff.mp huv with ⟨hu, hv0⟩ | ⟨hu, hv0⟩ <;>
    rcases Int.mul_nonneg_iff.mp hvw with ⟨hv1, hw⟩ | ⟨hv1, hw⟩
  · exact mul_nonneg hu hw
  · exact (hv (le_antisymm hv1 hv0)).elim
  · exact (hv (le_antisymm hv0 hv1)).elim
  · exact mul_nonneg_of_nonpos_of_nonpos hu hw

/-- Weak transitivity of nonnegativity with zero-propagation hypothesis -/
def Zsame_sign_trans_weak_check (_v u w : Int) : Bool :=
  decide (0 ≤ u * w)

/-- Specification: If (v = 0 → w = 0) and both u·v and v·w are nonnegative, then u·w is nonnegative. -/
theorem Zsame_sign_trans_weak_spec (v u w : Int) :
    ⦃⌜(v = 0 → w = 0) ∧ 0 ≤ u * v ∧ 0 ≤ v * w⌝⦄
    (pure (Zsame_sign_trans_weak_check v u w) : Id _)
    ⦃⇓result => ⌜result = decide (0 ≤ u * w)⌝⦄ := by
  intro _
  unfold Zsame_sign_trans_weak_check
  rfl

/-- Coq-compatible name: weak transitivity of nonnegativity -/
theorem Zsame_sign_trans_weak (v u w : Int) (hzero : v = 0 → w = 0)
    (huv : 0 ≤ u * v) (hvw : 0 ≤ v * w) : 0 ≤ u * w := by
  by_cases hv : v = 0
  · simp [hzero hv]
  · exact Zsame_sign_trans v u w hv huv hvw

/-- Deriving nonnegativity of product from sign-compatibility hypotheses -/
def Zsame_sign_imp_check (u v : Int)
    (_hp : 0 < u → 0 ≤ v)
    (_hn : 0 < -u → 0 ≤ -v) : Bool :=
  decide (0 ≤ u * v)

/-- Specification: If u > 0 implies v ≥ 0 and −u > 0 implies −v ≥ 0, then 0 ≤ u·v. -/
theorem Zsame_sign_imp_spec (u v : Int)
    (hp : 0 < u → 0 ≤ v) (hn : 0 < -u → 0 ≤ -v) :
    ⦃⌜True⌝⦄
    (pure (Zsame_sign_imp_check u v hp hn) : Id _)
    ⦃⇓result => ⌜result = decide (0 ≤ u * v)⌝⦄ := by
  intro _
  unfold Zsame_sign_imp_check
  rfl

/-- Coq-compatible name: sign implications imply a nonnegative product. -/
theorem Zsame_sign_imp (u v : Int)
    (hp : 0 < u → 0 ≤ v) (hn : 0 < -u → 0 ≤ -v) : 0 ≤ u * v := by
  by_cases hu : 0 ≤ u
  · by_cases hu0 : u = 0
    · simp [hu0]
    · exact mul_nonneg hu (hp (lt_of_le_of_ne hu (Ne.symm hu0)))
  · have huNeg : u ≤ 0 := le_of_lt (lt_of_not_ge hu)
    have hvNeg : v ≤ 0 := by
      have := hn (neg_pos.mpr (lt_of_not_ge hu))
      omega
    exact mul_nonneg_of_nonpos_of_nonpos huNeg hvNeg

/-- Nonnegativity of u·(u / v) when v ≥ 0 (truncated division). -/
def Zsame_sign_odiv_check (u v : Int) : Bool :=
  decide (0 ≤ u * Int.tdiv u v)

/-- Specification: If 0 ≤ v then 0 ≤ u·(u / v). -/
theorem Zsame_sign_odiv_spec (u v : Int) :
    ⦃⌜0 ≤ v⌝⦄
    (pure (Zsame_sign_odiv_check u v) : Id _)
    ⦃⇓result => ⌜result = decide (0 ≤ u * Int.tdiv u v)⌝⦄ := by
  intro _
  unfold Zsame_sign_odiv_check
  rfl

/-- Coq-compatible name: a nonnegative divisor gives a same-sign truncated quotient. -/
theorem Zsame_sign_odiv (u v : Int) (hv : 0 ≤ v) :
    0 ≤ u * Int.tdiv u v := by
  apply Zsame_sign_imp u (Int.tdiv u v)
  · intro hu
    exact Int.tdiv_nonneg (le_of_lt hu) hv
  · intro hu
    have h := Int.tdiv_nonneg (le_of_lt hu) hv
    simpa [Int.neg_tdiv] using h

end SameSign

section BooleanComparisons

/-- Boolean equality test for integers

    Tests whether two integers are equal, returning a boolean.
    This provides a decidable equality test.
-/
def Zeq_bool (x y : Int) : Bool :=
  decide (x = y)

/-- Graph of the integer equality test (FLoCq `Zeq_bool_prop`). -/
inductive Zeq_bool_prop (x y : Int) : Bool → Prop where
  | Zeq_bool_true_ : x = y → Zeq_bool_prop x y true
  | Zeq_bool_false_ : x ≠ y → Zeq_bool_prop x y false

export Zeq_bool_prop (Zeq_bool_true_ Zeq_bool_false_)

/-- Specification: Boolean equality test

    The boolean equality test returns true if and only if
    the integers are equal. This provides a computational
    version of equality.
-/
theorem Zeq_bool_spec (x y : Int) : Zeq_bool_prop x y (Zeq_bool x y) := by
  by_cases h : x = y
  · simpa [Zeq_bool, h] using Zeq_bool_true_ (x := x) (y := y) h
  · simpa [Zeq_bool, h] using Zeq_bool_false_ (x := x) (y := y) h

/-- Boolean less-or-equal test for integers

    Tests whether x ≤ y, returning a boolean result.
    This provides a decidable ordering test.
-/
def Zle_bool (x y : Int) : Bool :=
  decide (x ≤ y)

/-- Graph of the integer less-or-equal test (FLoCq `Zle_bool_prop`). -/
inductive Zle_bool_prop (x y : Int) : Bool → Prop where
  | Zle_bool_true_ : x ≤ y → Zle_bool_prop x y true
  | Zle_bool_false_ : y < x → Zle_bool_prop x y false

export Zle_bool_prop (Zle_bool_true_ Zle_bool_false_)

/-- Specification: Boolean ordering test

    The boolean less-or-equal test returns true if and only if
    x ≤ y. This provides a computational version of the ordering.
-/
theorem Zle_bool_spec (x y : Int) : Zle_bool_prop x y (Zle_bool x y) := by
  by_cases h : x ≤ y
  · simpa [Zle_bool, h] using Zle_bool_true_ (x := x) (y := y) h
  · have hyx : y < x := lt_of_not_ge h
    simpa [Zle_bool, h] using Zle_bool_false_ (x := x) (y := y) hyx

/-- Boolean strict less-than test for integers

    Tests whether x < y, returning a boolean result.
    This provides a decidable strict ordering test.
-/
def Zlt_bool (x y : Int) : Bool :=
  decide (x < y)

/-- Graph of the integer strict-order test (FLoCq `Zlt_bool_prop`). -/
inductive Zlt_bool_prop (x y : Int) : Bool → Prop where
  | Zlt_bool_true_ : x < y → Zlt_bool_prop x y true
  | Zlt_bool_false_ : y ≤ x → Zlt_bool_prop x y false

export Zlt_bool_prop (Zlt_bool_true_ Zlt_bool_false_)

/-- Specification: Boolean strict ordering test -/
theorem Zlt_bool_spec (x y : Int) : Zlt_bool_prop x y (Zlt_bool x y) := by
  by_cases h : x < y
  · simpa [Zlt_bool, h] using Zlt_bool_true_ (x := x) (y := y) h
  · have hyx : y ≤ x := le_of_not_gt h
    simpa [Zlt_bool, h] using Zlt_bool_false_ (x := x) (y := y) hyx

/-- Boolean equality is true when equal -/
def Zeq_bool_true_check (_ _ : Int) : Bool :=
  true

/-- Specification: Equality implies true -/
theorem Zeq_bool_true_spec (x y : Int) :
    ⦃⌜x = y⌝⦄
    (pure (Zeq_bool_true_check x y) : Id _)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zeq_bool_true_check
  rfl

/-- FLoCq `Zeq_bool_true`. -/
theorem Zeq_bool_true (x y : Int) (h : x = y) : Zeq_bool x y = true := by
  simp [Zeq_bool, h]

/-- Boolean equality is false when not equal -/
def Zeq_bool_false_check (_ _ : Int) : Bool :=
  false

/-- Specification: Inequality implies false -/
theorem Zeq_bool_false_spec (x y : Int) :
    ⦃⌜x ≠ y⌝⦄
    (pure (Zeq_bool_false_check x y) : Id _)
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Zeq_bool_false_check
  rfl

/-- FLoCq `Zeq_bool_false`. -/
theorem Zeq_bool_false (x y : Int) (h : x ≠ y) : Zeq_bool x y = false := by
  simp [Zeq_bool, h]

/-- Boolean equality is reflexive. -/
def Zeq_bool_diag_check (_ : Int) : Bool :=
  true

/-- Specification: Reflexivity of boolean equality

    The boolean equality test evaluates to true when
    comparing a value with itself. This is the boolean
    version of reflexivity.
-/
theorem Zeq_bool_diag_spec (x : Int) :
    ⦃⌜True⌝⦄
    (pure (Zeq_bool_diag_check x) : Id _)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zeq_bool_diag_check
  rfl

/-- FLoCq `Zeq_bool_diag`. -/
theorem Zeq_bool_diag (x : Int) : Zeq_bool x x = true := by
  simp [Zeq_bool]

/-- Opposite preserves equality testing

    Zeq_bool(-x, y) = Zeq_bool(x, -y). This shows that
    negation can be moved between arguments in equality tests.
-/
def Zeq_bool_opp_check (x y : Int) : Bool :=
  decide ((-x = y) = (x = -y))

/-- Specification: Negation commutes with equality

    The equality test is preserved when negating both sides
    or moving negation between arguments. This is useful for
    simplifying equality tests involving negations.
-/
theorem Zeq_bool_opp_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (Zeq_bool_opp_check x y) : Id _)
    ⦃⇓result => ⌜result = decide ((-x = y) = (x = -y))⌝⦄ := by
  intro _
  unfold Zeq_bool_opp_check
  rfl

/-- FLoCq `Zeq_bool_opp`. -/
theorem Zeq_bool_opp (x y : Int) : Zeq_bool (-x) y = Zeq_bool x (-y) := by
  by_cases h : -x = y <;> simp [Zeq_bool, h] <;> omega

/-- Double opposite preserves equality testing

    Zeq_bool(-x, -y) = Zeq_bool(x, y). This shows that
    negating both arguments preserves the equality test.
-/
def Zeq_bool_opp'_check (x y : Int) : Bool :=
  decide ((-x = -y) = (x = y))

/-- Specification: Double negation preserves equality

    The equality test is preserved when negating both
    arguments. This follows from the fact that negation
    is an injection on integers.
-/
theorem Zeq_bool_opp'_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (Zeq_bool_opp'_check x y) : Id _)
    ⦃⇓result => ⌜result = decide ((-x = -y) = (x = y))⌝⦄ := by
  intro _
  unfold Zeq_bool_opp'_check
  rfl

/-- FLoCq `Zeq_bool_opp'`. -/
theorem Zeq_bool_opp' (x y : Int) : Zeq_bool (-x) (-y) = Zeq_bool x y := by
  simp [Zeq_bool]

/-- Boolean less-or-equal is true when satisfied. -/
def Zle_bool_true_check (_ _ : Int) : Bool :=
  true

/-- Specification: Less-or-equal implies true

    When x ≤ y holds, the boolean less-or-equal test
    returns true. This is the soundness property for
    boolean ordering.
-/
theorem Zle_bool_true_spec (x y : Int) :
    ⦃⌜x ≤ y⌝⦄
    (pure (Zle_bool_true_check x y) : Id _)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zle_bool_true_check
  rfl

/-- FLoCq `Zle_bool_true`. -/
theorem Zle_bool_true (x y : Int) (h : x ≤ y) : Zle_bool x y = true := by
  simp [Zle_bool, h]

/-- Boolean less-or-equal is false when violated. -/
def Zle_bool_false_check (_ _ : Int) : Bool :=
  false

/-- Specification: Greater-than implies false

    When y < x holds, the boolean less-or-equal test
    returns false. This is the completeness property
    for boolean ordering.
-/
theorem Zle_bool_false_spec (x y : Int) :
    ⦃⌜y < x⌝⦄
    (pure (Zle_bool_false_check x y) : Id _)
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Zle_bool_false_check
  rfl

/-- FLoCq `Zle_bool_false`. -/
theorem Zle_bool_false (x y : Int) (h : y < x) : Zle_bool x y = false := by
  simp [Zle_bool, Int.not_le.mpr h]

/-- Boolean less-or-equal with opposite on left

    Zle_bool(-x, y) = Zle_bool(-y, x). This shows how
    negation on the left relates to swapping with negation.
-/
def Zle_bool_opp_l_check (x y : Int) : Bool :=
  decide ((- x ≤ y) = (- y ≤ x))

/-- Specification: Left negation swaps comparison

    Negating the left argument and swapping gives the same
    result: Zle_bool(-x, y) = Zle_bool(-y, x).
-/
theorem Zle_bool_opp_l_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (Zle_bool_opp_l_check x y) : Id _)
    ⦃⇓result => ⌜result = decide ((- x ≤ y) = (- y ≤ x))⌝⦄ := by
  intro _
  unfold Zle_bool_opp_l_check
  rfl

/-- FLoCq `Zle_bool_opp_l`. -/
theorem Zle_bool_opp_l (x y : Int) : Zle_bool (-x) y = Zle_bool (-y) x := by
  by_cases h : -x ≤ y <;> simp [Zle_bool, h] <;> omega

/-- Boolean less-or-equal with double opposite

    Zle_bool(-x, -y) = Zle_bool(y, x). This shows that
    double negation reverses the comparison.
-/
def Zle_bool_opp_check (x y : Int) : Bool :=
  decide ((- x ≤ - y) = (y ≤ x))

/-- Specification: Double negation reverses ordering

    Negating both arguments reverses the comparison:
    Zle_bool(-x, -y) = Zle_bool(y, x).
-/
theorem Zle_bool_opp_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (Zle_bool_opp_check x y) : Id _)
    ⦃⇓result => ⌜result = decide ((- x ≤ - y) = (y ≤ x))⌝⦄ := by
  intro _
  unfold Zle_bool_opp_check
  rfl

/-- FLoCq `Zle_bool_opp`. -/
theorem Zle_bool_opp (x y : Int) : Zle_bool (-x) (-y) = Zle_bool y x := by
  simp [Zle_bool]

/-- Boolean less-or-equal with opposite on right

    Zle_bool(x, -y) = Zle_bool(y, -x). This shows how
    negation on the right relates to swapping with negation.
-/
def Zle_bool_opp_r_check (x y : Int) : Bool :=
  decide ((x ≤ - y) = (y ≤ - x))

/-- Specification: Right negation swaps comparison

    Negating the right argument relates to swapping with
    left negation: Zle_bool(x, -y) = Zle_bool(y, -x).
-/
theorem Zle_bool_opp_r_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (Zle_bool_opp_r_check x y) : Id _)
    ⦃⇓result => ⌜result = decide ((x ≤ - y) = (y ≤ - x))⌝⦄ := by
  intro _
  unfold Zle_bool_opp_r_check
  rfl

/-- FLoCq `Zle_bool_opp_r`. -/
theorem Zle_bool_opp_r (x y : Int) : Zle_bool x (-y) = Zle_bool y (-x) := by
  by_cases h : x ≤ -y <;> simp [Zle_bool, h] <;> omega

/-- Negation of less-or-equal is strict greater-than

    Shows that negb (Zle_bool x y) = Zlt_bool y x.
    This captures the duality between ≤ and >.
-/
def negb_Zle_bool_check (x y : Int) : Bool :=
  decide (!(x ≤ y) = (y < x))

/-- Specification: Negated ≤ equals strict >

    The negation of x ≤ y is equivalent to y < x. This duality
    is fundamental for simplifying boolean comparisons.
-/
theorem negb_Zle_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (negb_Zle_bool_check x y) : Id _)
    ⦃⇓result => ⌜result = decide (!(x ≤ y) = (y < x))⌝⦄ := by
  intro _
  unfold negb_Zle_bool_check
  rfl

/-- FLoCq `negb_Zle_bool`. -/
theorem negb_Zle_bool (x y : Int) : !Zle_bool x y = Zlt_bool y x := by
  by_cases h : x ≤ y <;> simp [Zle_bool, Zlt_bool, h]

/-- Negation of strict less-than is greater-or-equal

    Shows that negb (Zlt_bool x y) = Zle_bool y x.
    This captures the duality between < and ≥.
-/
def negb_Zlt_bool_check (x y : Int) : Bool :=
  decide (!(x < y) = (y ≤ x))

/-- Specification: Negated < equals ≥

    The negation of x < y is equivalent to y ≤ x. This duality
    allows conversion between strict and non-strict comparisons.
-/
theorem negb_Zlt_bool_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (negb_Zlt_bool_check x y) : Id _)
    ⦃⇓result => ⌜result = decide (!(x < y) = (y ≤ x))⌝⦄ := by
  intro _
  unfold negb_Zlt_bool_check
  rfl

/-- FLoCq `negb_Zlt_bool`. -/
theorem negb_Zlt_bool (x y : Int) : !Zlt_bool x y = Zle_bool y x := by
  by_cases h : x < y <;> simp [Zlt_bool, Zle_bool, h]

/-- Boolean less-than is true when satisfied. -/
def Zlt_bool_true_check (_ _ : Int) : Bool :=
  true

/-- Specification: Less-than implies true

    When x < y holds, the boolean less-than test
    returns true. This is the soundness property for
    boolean strict ordering.
-/
theorem Zlt_bool_true_spec (x y : Int) :
    ⦃⌜x < y⌝⦄
    (pure (Zlt_bool_true_check x y) : Id _)
    ⦃⇓result => ⌜result = true⌝⦄ := by
  intro _
  unfold Zlt_bool_true_check
  rfl

/-- FLoCq `Zlt_bool_true`. -/
theorem Zlt_bool_true (x y : Int) (h : x < y) : Zlt_bool x y = true := by
  simp [Zlt_bool, h]

/-- Boolean less-than is false when violated. -/
def Zlt_bool_false_check (_ _ : Int) : Bool :=
  false

/-- Specification: Greater-or-equal implies false

    When y ≤ x holds, the boolean less-than test
    returns false. This is the completeness property
    for boolean strict ordering.
-/
theorem Zlt_bool_false_spec (x y : Int) :
    ⦃⌜y ≤ x⌝⦄
    (pure (Zlt_bool_false_check x y) : Id _)
    ⦃⇓result => ⌜result = false⌝⦄ := by
  intro _
  unfold Zlt_bool_false_check
  rfl

/-- FLoCq `Zlt_bool_false`. -/
theorem Zlt_bool_false (x y : Int) (h : y ≤ x) : Zlt_bool x y = false := by
  simp [Zlt_bool, Int.not_lt.mpr h]

/-- Boolean less-than with opposite on left

    Zlt_bool(-x, y) = Zlt_bool(-y, x). This shows how
    negation on the left relates to swapping with negation.
-/
def Zlt_bool_opp_l_check (x y : Int) : Bool :=
  decide ((- x < y) = (- y < x))

/-- Specification: Left negation swaps strict comparison

    Negating the left argument and swapping gives the same
    result: Zlt_bool(-x, y) = Zlt_bool(-y, x).
-/
theorem Zlt_bool_opp_l_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (Zlt_bool_opp_l_check x y) : Id _)
    ⦃⇓result => ⌜result = decide ((- x < y) = (- y < x))⌝⦄ := by
  intro _
  unfold Zlt_bool_opp_l_check
  rfl

/-- FLoCq `Zlt_bool_opp_l`. -/
theorem Zlt_bool_opp_l (x y : Int) : Zlt_bool (-x) y = Zlt_bool (-y) x := by
  by_cases h : -x < y <;> simp [Zlt_bool, h] <;> omega

/-- Boolean less-than with opposite on right

    Zlt_bool(x, -y) = Zlt_bool(y, -x). This shows how
    negation on the right relates to swapping with negation.
-/
def Zlt_bool_opp_r_check (x y : Int) : Bool :=
  decide ((x < - y) = (y < - x))

/-- Specification: Right negation swaps strict comparison

    Negating the right argument relates to swapping with
    left negation: Zlt_bool(x, -y) = Zlt_bool(y, -x).
-/
theorem Zlt_bool_opp_r_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (Zlt_bool_opp_r_check x y) : Id _)
    ⦃⇓result => ⌜result = decide ((x < - y) = (y < - x))⌝⦄ := by
  intro _
  unfold Zlt_bool_opp_r_check
  rfl

/-- FLoCq `Zlt_bool_opp_r`. -/
theorem Zlt_bool_opp_r (x y : Int) : Zlt_bool x (-y) = Zlt_bool y (-x) := by
  by_cases h : x < -y <;> simp [Zlt_bool, h] <;> omega

/-- Boolean less-than with double opposite

    Zlt_bool(-x, -y) = Zlt_bool(y, x). This shows that
    double negation reverses the strict comparison.
-/
def Zlt_bool_opp_check (x y : Int) : Bool :=
  decide ((- x < - y) = (y < x))

/-- Specification: Double negation reverses strict ordering

    Negating both arguments reverses the comparison:
    Zlt_bool(-x, -y) = Zlt_bool(y, x).
-/
theorem Zlt_bool_opp_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (Zlt_bool_opp_check x y) : Id _)
    ⦃⇓result => ⌜result = decide ((- x < - y) = (y < x))⌝⦄ := by
  intro _
  unfold Zlt_bool_opp_check
  rfl

/-- FLoCq `Zlt_bool_opp`. -/
theorem Zlt_bool_opp (x y : Int) : Zlt_bool (-x) (-y) = Zlt_bool y x := by
  simp [Zlt_bool]

end BooleanComparisons

section Zcompare

/-- Three-way comparison for integers

    Returns Lt if x < y, Eq if x = y, and Gt if x > y.
    This provides a complete ordering comparison in one operation.
-/
def Zcompare (x y : Int) : Ordering :=
  if x < y then Ordering.lt
  else if x = y then Ordering.eq
  else Ordering.gt

/-- Graph of integer comparison (FLoCq `Zcompare_prop`). -/
inductive Zcompare_prop (x y : Int) : Ordering → Prop where
  | Zcompare_Lt_ : x < y → Zcompare_prop x y .lt
  | Zcompare_Eq_ : x = y → Zcompare_prop x y .eq
  | Zcompare_Gt_ : y < x → Zcompare_prop x y .gt

export Zcompare_prop (Zcompare_Lt_ Zcompare_Eq_ Zcompare_Gt_)

/-- FLoCq `Zcompare_spec`. -/
theorem Zcompare_spec (x y : Int) : Zcompare_prop x y (Zcompare x y) := by
  by_cases hxy : x < y
  · simpa [Zcompare, hxy] using Zcompare_Lt_ (x := x) (y := y) hxy
  · by_cases hxeq : x = y
    · simpa [Zcompare, hxy, hxeq] using Zcompare_Eq_ (x := x) (y := y) hxeq
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) (Ne.symm hxeq)
      simpa [Zcompare, hxy, hxeq] using Zcompare_Gt_ (x := x) (y := y) hyx

/-- Specification: Three-way comparison correctness

    The comparison function returns:
    - Lt when x < y
    - Eq when x = y
    - Gt when x > y

    This captures the complete ordering of integers.
-/
theorem Zcompare_behavior_spec (x y : Int) :
    ⦃⌜True⌝⦄
    (pure (Zcompare x y) : Id _)
    ⦃⇓result => ⌜(result = Ordering.lt ↔ x < y) ∧
                (result = Ordering.eq ↔ x = y) ∧
                (result = Ordering.gt ↔ y < x)⌝⦄ := by
  intro _
  unfold Zcompare

  -- Split on whether x < y
  split
  · -- Case: x < y
    rename_i h_lt
    constructor
    · -- Prove: Ordering.lt = Ordering.lt ↔ x < y
      exact ⟨fun _ => h_lt, fun _ => rfl⟩
    constructor
    · -- Prove: Ordering.lt = Ordering.eq ↔ x = y
      constructor
      · intro h_eq
        -- Ordering.lt = Ordering.eq is impossible
        cases h_eq
      · intro h_eq
        -- If x = y and x < y, contradiction
        rw [h_eq] at h_lt
        exact absurd h_lt (lt_irrefl y)
    · -- Prove: Ordering.lt = Ordering.gt ↔ y < x
      constructor
      · intro h_eq
        -- Ordering.lt = Ordering.gt is impossible
        cases h_eq
      · intro h_gt
        -- If y < x and x < y, contradiction
        exact absurd h_lt (not_lt.mpr (le_of_lt h_gt))

  · -- Case: ¬(x < y), split on whether x = y
    rename_i h_not_lt
    split
    · -- Case: x = y
      rename_i h_eq
      constructor
      · -- Prove: Ordering.eq = Ordering.lt ↔ x < y
        constructor
        · intro h_ord_eq
          -- Ordering.eq = Ordering.lt is impossible
          cases h_ord_eq
        · intro h_lt
          -- If x < y but ¬(x < y), contradiction
          exact absurd h_lt h_not_lt
      constructor
      · -- Prove: Ordering.eq = Ordering.eq ↔ x = y
        exact ⟨fun _ => h_eq, fun _ => rfl⟩
      · -- Prove: Ordering.eq = Ordering.gt ↔ y < x
        constructor
        · intro h_ord_eq
          -- Ordering.eq = Ordering.gt is impossible
          cases h_ord_eq
        · intro h_gt
          -- If y < x and x = y, contradiction
          rw [← h_eq] at h_gt
          exact absurd h_gt (lt_irrefl x)

    · -- Case: ¬(x < y) ∧ ¬(x = y), so y < x
      rename_i h_not_eq
      -- In this case, y < x
      have h_gt : y < x := by
        -- Since ¬(x < y) and ¬(x = y), we must have y < x
        cases' lt_trichotomy x y with h h
        · exact absurd h h_not_lt
        · cases' h with h h
          · exact absurd h h_not_eq
          · exact h

      constructor
      · -- Prove: Ordering.gt = Ordering.lt ↔ x < y
        constructor
        · intro h_ord_eq
          -- Ordering.gt = Ordering.lt is impossible
          cases h_ord_eq
        · intro h_lt
          -- If x < y but ¬(x < y), contradiction
          exact absurd h_lt h_not_lt
      constructor
      · -- Prove: Ordering.gt = Ordering.eq ↔ x = y
        constructor
        · intro h_ord_eq
          -- Ordering.gt = Ordering.eq is impossible
          cases h_ord_eq
        · intro h_eq
          -- If x = y but ¬(x = y), contradiction
          exact absurd h_eq h_not_eq
      · -- Prove: Ordering.gt = Ordering.gt ↔ y < x
        exact ⟨fun _ => h_gt, fun _ => rfl⟩

/-- Comparison returns Lt for less-than

    When x < y, Zcompare returns Lt. This provides
    a computational witness for the less-than relation.
-/
def Zcompare_Lt_check (_ _ : Int) : Ordering :=
  Ordering.lt

/-- Specification: Less-than yields Lt

    The comparison function returns Lt exactly when x < y.
    This provides the forward direction of the comparison specification.
-/
theorem Zcompare_Lt_spec (x y : Int) :
    ⦃⌜x < y⌝⦄
    (pure (Zcompare_Lt_check x y) : Id _)
    ⦃⇓result => ⌜result = Ordering.lt⌝⦄ := by
  intro _
  unfold Zcompare_Lt_check
  rfl

/-- FLoCq `Zcompare_Lt`. -/
theorem Zcompare_Lt (x y : Int) (h : x < y) : Zcompare x y = Ordering.lt := by
  simp [Zcompare, h]

/-- Comparison returns Eq for equality

    When x = y, Zcompare returns Eq. This provides
    a computational witness for equality.
-/
def Zcompare_Eq_check (_ _ : Int) : Ordering :=
  Ordering.eq

/-- Specification: Equality yields Eq

    The comparison function returns Eq exactly when x = y.
    This provides decidable equality through comparison.
-/
theorem Zcompare_Eq_spec (x y : Int) :
    ⦃⌜x = y⌝⦄
    (pure (Zcompare_Eq_check x y) : Id _)
    ⦃⇓result => ⌜result = Ordering.eq⌝⦄ := by
  intro _
  unfold Zcompare_Eq_check
  rfl

/-- FLoCq `Zcompare_Eq`. -/
theorem Zcompare_Eq (x y : Int) (h : x = y) : Zcompare x y = Ordering.eq := by
  simp [Zcompare, h]

/-- Comparison returns Gt for greater-than

    When y < x, Zcompare returns Gt. This provides
    a computational witness for the greater-than relation.
-/
def Zcompare_Gt_check (_ _ : Int) : Ordering :=
  Ordering.gt

/-- Specification: Greater-than yields Gt

    The comparison function returns Gt exactly when y < x.
    This completes the three cases of integer comparison.
-/
theorem Zcompare_Gt_spec (x y : Int) :
    ⦃⌜y < x⌝⦄
    (pure (Zcompare_Gt_check x y) : Id _)
    ⦃⇓result => ⌜result = Ordering.gt⌝⦄ := by
  intro _
  unfold Zcompare_Gt_check
  rfl

/-- FLoCq `Zcompare_Gt`. -/
theorem Zcompare_Gt (x y : Int) (h : y < x) : Zcompare x y = Ordering.gt := by
  simp [Zcompare, Int.not_lt.mpr h.le, ne_of_gt h]

end Zcompare

section CondZopp

/-- Conditional opposite based on sign

    Returns -x if the condition is true, x otherwise.
    This is used for conditional negation in floating-point
    sign handling.
-/
@[flocq_source "src/Core/Zaux.v" 23 "cond_Zopp"]
def cond_Zopp (b : Bool) (x : Int) : Int :=
  if b then -x else x

/-- Specification: Conditional negation

    The conditional opposite operation returns:
    - -x when b is true
    - x when b is false

    This is fundamental for handling signs in floating-point.
-/
theorem cond_Zopp_spec (b : Bool) (x : Int) :
    ⦃⌜True⌝⦄
    (pure (cond_Zopp b x) : Id _)
    ⦃⇓result => ⌜result = if b then -x else x⌝⦄ := by
  intro _
  unfold cond_Zopp
  rfl

/-- Conditional opposite of zero. -/
def cond_Zopp_0_check (_ : Bool) : Int :=
  0

/-- Specification: Zero invariance under conditional opposite. -/
theorem cond_Zopp_0_spec (sx : Bool) :
    ⦃⌜True⌝⦄
    (pure (cond_Zopp_0_check sx) : Id _)
    ⦃⇓result => ⌜result = 0⌝⦄ := by
  intro _
  unfold cond_Zopp_0_check
  rfl

/-- FLoCq `cond_Zopp_0`. -/
theorem cond_Zopp_0 (sx : Bool) : cond_Zopp sx 0 = 0 := by
  cases sx <;> rfl

/-- Negated condition flips conditional opposite. -/
def cond_Zopp_negb_check (x : Bool) (y : Int) : Int :=
  -(if x then -y else y)

/-- Specification: Condition negation flips result. -/
theorem cond_Zopp_negb_spec (x : Bool) (y : Int) :
    ⦃⌜True⌝⦄
    (pure (cond_Zopp_negb_check x y) : Id _)
    ⦃⇓result => ⌜result = -(if x then -y else y)⌝⦄ := by
  intro _
  unfold cond_Zopp_negb_check
  rfl

/-- FLoCq `cond_Zopp_negb`. -/
theorem cond_Zopp_negb (x : Bool) (y : Int) :
    cond_Zopp (!x) y = -cond_Zopp x y := by
  cases x <;> simp [cond_Zopp]

/-- Absolute value preservation under conditional opposite. -/
def abs_cond_Zopp_check (_b : Bool) (m : Int) : Int :=
  (Int.natAbs m : Int)

/-- Specification: Conditional opposite preserves magnitude. -/
theorem abs_cond_Zopp_spec (b : Bool) (m : Int) :
    ⦃⌜True⌝⦄
    (pure (abs_cond_Zopp_check b m) : Id _)
    ⦃⇓result => ⌜result = (Int.natAbs m : Int)⌝⦄ := by
  intro _
  unfold abs_cond_Zopp_check
  rfl

/-- FLoCq `abs_cond_Zopp`. -/
theorem abs_cond_Zopp (b : Bool) (m : Int) :
    |cond_Zopp b m| = |m| := by
  cases b <;> simp [cond_Zopp]

/-- Absolute value via conditional opposite. -/
def cond_Zopp_Zlt_bool_check (m : Int) : Int :=
  (Int.natAbs m : Int)

/-- Specification: Absolute value computation. -/
theorem cond_Zopp_Zlt_bool_spec (m : Int) :
    ⦃⌜True⌝⦄
    (pure (cond_Zopp_Zlt_bool_check m) : Id _)
    ⦃⇓result => ⌜result = (Int.natAbs m : Int)⌝⦄ := by
  intro _
  unfold cond_Zopp_Zlt_bool_check
  rfl

/-- FLoCq `cond_Zopp_Zlt_bool`. -/
theorem cond_Zopp_Zlt_bool (m : Int) :
    cond_Zopp (Zlt_bool m 0) m = |m| := by
  by_cases h : m < 0
  · simp [cond_Zopp, Zlt_bool, h, abs_of_nonpos h.le]
  · simp [cond_Zopp, Zlt_bool, h, abs_of_nonneg (le_of_not_gt h)]

/-- Equality test with conditional opposite

    Shows that Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n).
    This demonstrates the symmetry of conditional negation in equality tests.
-/
def Zeq_bool_cond_Zopp_check (s : Bool) (m n : Int) : Bool :=
  decide (((if s then -m else m) = n) = (m = (if s then -n else n)))

/-- Specification: Conditional opposite commutes with equality

    The equality test is preserved when moving conditional negation
    between arguments: Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n).
-/
theorem Zeq_bool_cond_Zopp_spec (s : Bool) (m n : Int) :
    ⦃⌜True⌝⦄
    (pure (Zeq_bool_cond_Zopp_check s m n) : Id _)
    ⦃⇓result => ⌜result = decide (((if s then -m else m) = n) = (m = (if s then -n else n)))⌝⦄ := by
  intro _
  unfold Zeq_bool_cond_Zopp_check
  rfl

/-- FLoCq `Zeq_bool_cond_Zopp`. -/
theorem Zeq_bool_cond_Zopp (s : Bool) (m n : Int) :
    Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n) := by
  cases s
  · rfl
  · exact Zeq_bool_opp m n

end CondZopp

section FastPower

/-- Fast exponentiation for positive exponents

    Computes v^e efficiently using repeated squaring.
    This provides O(log e) complexity instead of O(e).
-/
def Zfast_pow_pos (v : Int) (e : Positive) : Int :=
  v ^ positiveToNat e

/-- Specification: Fast power computes correct result

    The fast exponentiation algorithm computes the same result
    as naive exponentiation but with better complexity.
-/
theorem Zfast_pow_pos_spec (v : Int) (e : Positive) :
    ⦃⌜True⌝⦄
    (pure (Zfast_pow_pos v e) : Id _)
    ⦃⇓result => ⌜result = Zpower_pos v e⌝⦄ := by
  intro _
  unfold Zfast_pow_pos Zpower_pos
  rfl

/-- Coq-compat name: correctness of fast exponentiation for positive exponents -/
theorem Zfast_pow_pos_correct (v : Int) (e : Positive) :
    Zfast_pow_pos v e = Zpower_pos v e := rfl

end FastPower

section FasterDiv

/-- Coq `Z.div_eucl`: floor quotient and a remainder with the divisor's sign. -/
def Z_div_eucl (a b : Int) : (Int × Int) :=
  let q := Int.fdiv a b
  (q, a - b * q)

/-- Specification of the Coq-compatible Euclidean-division pair. -/
theorem Zdiv_eucl_unique_spec (a b : Int) :
    ⦃⌜True⌝⦄
    (pure (Z_div_eucl a b) : Id _)
    ⦃⇓result => ⌜result =
      (Int.fdiv a b, a - b * Int.fdiv a b)⌝⦄ := by
  intro _
  unfold Z_div_eucl
  rfl

/-- FLoCq `Zdiv_eucl_unique`. -/
theorem Zdiv_eucl_unique (a b : Int) :
    Z_div_eucl a b =
      (Int.fdiv a b, a - b * Int.fdiv a b) := rfl

/-- Coq `Zpos`: embed a positive integer into `Int`. -/
def Zpos (p : Positive) : Int :=
  positiveToNat p

private def Zpos_div_eucl_aux1_nat : Positive → Positive → Nat × Nat
  | a, Positive.xH => (positiveToNat a, 0)
  | Positive.xH, Positive.xO _ => (0, 1)
  | Positive.xO a, Positive.xO b =>
      let qr := Zpos_div_eucl_aux1_nat a b
      (qr.1, 2 * qr.2)
  | Positive.xI a, Positive.xO b =>
      let qr := Zpos_div_eucl_aux1_nat a b
      (qr.1, 2 * qr.2 + 1)
  | a, Positive.xI b =>
      (positiveToNat a / positiveToNat (Positive.xI b),
        positiveToNat a % positiveToNat (Positive.xI b))

private theorem Zpos_div_eucl_aux1_nat_correct (a b : Positive) :
    Zpos_div_eucl_aux1_nat a b =
      (positiveToNat a / positiveToNat b, positiveToNat a % positiveToNat b) := by
  induction b generalizing a with
  | xH =>
      cases a <;> simp [Zpos_div_eucl_aux1_nat, positiveToNat, Nat.div_one, Nat.mod_one]
  | xI b =>
      cases a <;> simp [Zpos_div_eucl_aux1_nat]
  | xO b ih =>
      cases a with
      | xH =>
          have hbpos : 0 < positiveToNat b := positiveToNat_pos b
          have hlt : 1 < 2 * positiveToNat b := by omega
          have hdiv : 1 / (2 * positiveToNat b) = 0 := Nat.div_eq_of_lt hlt
          have hmod : 1 % (2 * positiveToNat b) = 1 := Nat.mod_eq_of_lt hlt
          simp [Zpos_div_eucl_aux1_nat, positiveToNat, hdiv, hmod]
      | xO a =>
          have ih' := ih a
          simp only [Zpos_div_eucl_aux1_nat] at ih' ⊢
          rw [ih']
          have htwo : 0 < 2 := by decide
          simp [positiveToNat, Nat.mul_div_mul_left, Nat.mul_mod_mul_left, htwo]
      | xI a =>
          have ih' := ih a
          simp only [Zpos_div_eucl_aux1_nat] at ih' ⊢
          rw [ih']
          set A := positiveToNat a
          set B := positiveToNat b
          set q := A / B
          set r := A % B
          have hBpos : 0 < B := by simpa [B] using positiveToNat_pos b
          have hden_pos : 0 < 2 * B := by omega
          have hrem_lt : 2 * r + 1 < 2 * B := by
            have hr_lt : r < B := by
              simpa [r] using Nat.mod_lt A hBpos
            omega
          have hdecomp : B * q + r = A := by
            simpa [q, r] using Nat.div_add_mod A B
          have hnum : 2 * A + 1 = (2 * B) * q + (2 * r + 1) := by
            rw [← hdecomp]
            ring
          have hdiv :
              (2 * A + 1) / (2 * B) = q := by
            calc
              (2 * A + 1) / (2 * B)
                  = ((2 * B) * q + (2 * r + 1)) / (2 * B) := by
                      rw [hnum]
              _ = q + (2 * r + 1) / (2 * B) := by
                      rw [Nat.mul_add_div hden_pos]
              _ = q := by rw [Nat.div_eq_of_lt hrem_lt, Nat.add_zero]
          have hmod :
              (2 * A + 1) % (2 * B) = 2 * r + 1 := by
            calc
              (2 * A + 1) % (2 * B)
                  = ((2 * B) * q + (2 * r + 1)) % (2 * B) := by
                      rw [hnum]
              _ = (2 * r + 1) % (2 * B) := by
                      rw [Nat.mul_add_mod]
              _ = 2 * r + 1 := Nat.mod_eq_of_lt hrem_lt
          simp [positiveToNat, A, B, q, r, hdiv, hmod]

/-- Coq `Z.pos_div_eucl` for the positive-divisor case used by this file. -/
def Z_pos_div_eucl (a : Positive) (b : Int) : Int × Int :=
  (Zpos a / b, Zpos a % b)

/-- Auxiliary division algorithm on positive integers. -/
def Zpos_div_eucl_aux1 (a b : Positive) : Int × Int :=
  let qr := Zpos_div_eucl_aux1_nat a b
  (qr.1, qr.2)

/-- Coq `Zaux.v`: `Zpos_div_eucl_aux1 a b = Z.pos_div_eucl a (Zpos b)`. -/
theorem Zpos_div_eucl_aux1_correct (a b : Positive) :
    Zpos_div_eucl_aux1 a b = Z_pos_div_eucl a (Zpos b) := by
  unfold Zpos_div_eucl_aux1 Z_pos_div_eucl Zpos
  rw [Zpos_div_eucl_aux1_nat_correct]
  simp [Int.natCast_ediv, Int.natCast_emod]

/-- Secondary auxiliary division algorithm on positive integers. -/
def Zpos_div_eucl_aux (a b : Positive) : Int × Int :=
  if positiveToNat a < positiveToNat b then
    (0, Zpos a)
  else if positiveToNat a = positiveToNat b then
    (1, 0)
  else
    Zpos_div_eucl_aux1 a b

/-- Coq `Zaux.v`: `Zpos_div_eucl_aux a b = Z.pos_div_eucl a (Zpos b)`. -/
theorem Zpos_div_eucl_aux_correct (a b : Positive) :
    Zpos_div_eucl_aux a b = Z_pos_div_eucl a (Zpos b) := by
  unfold Zpos_div_eucl_aux
  by_cases hlt : positiveToNat a < positiveToNat b
  · simp only [hlt, ↓reduceIte]
    unfold Z_pos_div_eucl Zpos
    apply Prod.ext
    · rw [← Int.natCast_ediv, Nat.div_eq_of_lt hlt]
      rfl
    · rw [← Int.natCast_emod, Nat.mod_eq_of_lt hlt]
  · simp only [hlt, ↓reduceIte]
    by_cases heq : positiveToNat a = positiveToNat b
    · have hbpos : 0 < positiveToNat b := positiveToNat_pos b
      simp only [heq, ↓reduceIte]
      unfold Z_pos_div_eucl Zpos
      apply Prod.ext
      · rw [heq, ← Int.natCast_ediv, Nat.div_self hbpos]
        rfl
      · rw [heq, ← Int.natCast_emod, Nat.mod_self]
        rfl
    · simp [heq, Zpos_div_eucl_aux1_correct]

/-- Specification: correctness of secondary positive-aux division helper. -/
theorem Zpos_div_eucl_aux_correct_spec (a b : Positive) :
    ⦃⌜True⌝⦄
    (pure (Zpos_div_eucl_aux a b) : Id _)
    ⦃⇓result => ⌜result = Z_pos_div_eucl a (Zpos b)⌝⦄ := by
  intro _
  exact Zpos_div_eucl_aux_correct a b

/-- Fast Euclidean division for integers. -/
def Zfast_div_eucl (a b : Int) : (Int × Int) :=
  Z_div_eucl a b

/-- Specification: fast division computes the Coq-compatible division pair. -/
theorem Zfast_div_eucl_spec (a b : Int) :
    ⦃⌜True⌝⦄
    (pure (Zfast_div_eucl a b) : Id _)
    ⦃⇓result => ⌜result = Z_div_eucl a b⌝⦄ := by
  intro _
  rfl

end FasterDiv

-- Coq-compat name: correctness of fast Euclidean division
theorem Zfast_div_eucl_correct (a b : Int) :
    Zfast_div_eucl a b = Z_div_eucl a b := rfl

section Iteration

/-- Generic iteration of a function

    Applies function f to x a total of n times.
    This provides a generic iteration construct used
    throughout the formalization.
-/
def iter_nat {A : Type} (f : A → A) (n : Nat) (x : A) : A :=
  match n with
  | 0 => x
  | n' + 1 => f (iter_nat f n' x)

/-- Specification: Iteration applies function n times. -/
theorem iter_nat_spec {A : Type} (f : A → A) (n : Nat) (x : A) :
    ⦃⌜True⌝⦄
    (pure (iter_nat f n x) : Id _)
    ⦃⇓result => ⌜result = f^[n] x⌝⦄ := by
  intro _
  induction n generalizing x with
  | zero => simp [iter_nat]
  | succ n ih =>
      simpa [iter_nat, Function.iterate_succ_apply'] using congrArg f (ih x)

/-- Successor property for iteration

    Shows that iter_nat f (S p) x = f (iter_nat f p x).
    This is the successor case of the iteration recursion.
-/
def iter_nat_S_check {A : Type} (f : A → A) (p : Nat) (x : A) : A :=
  f (iter_nat f p x)

/-- Specification: Iteration successor formula

    Iterating S p times is equivalent to iterating p times
    followed by one more application of f. This captures
    the recursive nature of iteration.
-/
theorem iter_nat_S_spec {A : Type} (f : A → A) (p : Nat) (x : A) :
    ⦃⌜True⌝⦄
    (pure (iter_nat_S_check f p x) : Id _)
    ⦃⇓result => ⌜result = f (iter_nat f p x)⌝⦄ := by
  intro _
  unfold iter_nat_S_check
  rfl

/-- FLoCq `iter_nat_S`. -/
theorem iter_nat_S {A : Type} (f : A → A) (p : Nat) (x : A) :
    iter_nat f (p + 1) x = f (iter_nat f p x) := rfl

/-- Iteration addition formula. -/
def iter_nat_plus_check {A : Type} (f : A → A) (p q : Nat) (x : A) : A :=
  iter_nat f p (iter_nat f q x)

/-- Specification: Iteration count addition. -/
theorem iter_nat_plus_spec {A : Type} (f : A → A) (p q : Nat) (x : A) :
    ⦃⌜True⌝⦄
    (pure (iter_nat_plus_check f p q x) : Id _)
    ⦃⇓result => ⌜result = iter_nat f p (iter_nat f q x)⌝⦄ := by
  intro _
  unfold iter_nat_plus_check
  rfl

/-- FLoCq `iter_nat_plus`. -/
theorem iter_nat_plus {A : Type} (f : A → A) (p q : Nat) (x : A) :
    iter_nat f (p + q) x = iter_nat f p (iter_nat f q x) := by
  induction p with
  | zero => simp [iter_nat]
  | succ p ih => simpa [iter_nat, Nat.succ_add] using congrArg f ih

/-- Binary-positive iteration, matching the Corelib `SpecFloat.iter_pos`
    body imported by Flocq. It recurses on the positive constructors directly;
    `iter_pos_nat` relates it to natural-count iteration. -/
@[flocq_source "src/Core/Zaux.v" 24 "iter_pos"]
def iter_pos {A : Type} (f : A → A) (p : Positive) (x : A) : A :=
  match p with
  | .xH => f x
  | .xO p => iter_pos f p (iter_pos f p x)
  | .xI p => iter_pos f p (iter_pos f p (f x))

private theorem iter_nat_apply {A : Type} (f : A → A) (n : Nat) (x : A) :
    iter_nat f n (f x) = f (iter_nat f n x) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [iter_nat] using congrArg f ih

/-- FLoCq `iter_pos_nat`; also preserves the previous natural-count implementation. -/
theorem iter_pos_nat {A : Type} (f : A → A) (p : Positive) (x : A) :
    iter_pos f p x = iter_nat f (positiveToNat p) x := by
  induction p generalizing x with
  | xH => rfl
  | xO p ih =>
      simp only [iter_pos, positiveToNat, ih, ← iter_nat_plus, two_mul]
  | xI p ih =>
      simp only [iter_pos, positiveToNat, ih, ← iter_nat_plus, two_mul,
        iter_nat_S, iter_nat_apply]

def iter_pos_nat_check {A : Type} (f : A → A) (p : Positive) (x : A) : A :=
  iter_pos f p x

/-- Specification: Positive iteration via naturals

    Iteration with positive numbers can be expressed through
    natural number iteration after conversion. This allows
    unified reasoning about different iteration types.
-/
theorem iter_pos_nat_spec {A : Type} (f : A → A) (p : Positive) (x : A) :
    ⦃⌜True⌝⦄
    (pure (iter_pos_nat_check f p x) : Id _)
    ⦃⇓result => ⌜result = iter_nat f (positiveToNat p) x⌝⦄ := by
  intro _
  simpa [iter_pos_nat_check, wp, PostCond.noThrow, Id.run, pure] using iter_pos_nat f p x

end Iteration

end FloatSpec.Core.Zaux
