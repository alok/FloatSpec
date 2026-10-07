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

/-- Rocq's Boolean parity test `Z.even : Z → bool`: `true` exactly on the even integers.
Flocq states parity with it, for example in `Zeven_ex` below, `ZnearestE` (Round_NE.v) and
`Rnd_odd_pt` (Round_odd.v). The Rocq function matches on the binary constructors of `Z`;
Lean's `Int` has no binary constructors, so the port decides divisibility by two. -/
@[flocq_local "Rocq Corelib BinNums.IntDef.Z.even (Stdlib Z.even : Z -> bool); not defined in Flocq itself"]
def Z.even (z : Int) : Bool :=
  decide (2 ∣ z)

/-- Rocq's `Z.even_spec`, with Mathlib's `Even` for Rocq's `Z.Even`: the Boolean parity test is
`true` exactly on the even integers. -/
theorem Z.even_spec (n : Int) : Z.even n = true ↔ Even n := by
  simp [Z.even, even_iff_two_dvd]

/-- FLoCq `Zeven_ex`. -/
@[flocq_source "src/Core/Zaux.v" 75 "Zeven_ex"]
theorem Zeven_ex (x : Int) :
    ∃ p : Int, x = 2 * p + if Z.even x then 0 else 1 := by
  refine ⟨x / 2, ?_⟩
  have hdiv := Int.emod_add_mul_ediv x 2
  rcases Int.emod_two_eq_zero_or_one x with hrem | hrem
  · have heven : Z.even x = true := by simp [Z.even, Int.dvd_iff_emod_eq_zero, hrem]
    simp only [heven, ↓reduceIte]
    omega
  · have hodd : Z.even x = false := by simp [Z.even, Int.dvd_iff_emod_eq_zero, hrem]
    simp only [hodd, Bool.false_eq_true, ↓reduceIte]
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

    If 0 < b and p is a binary positive, then b^p > 0.
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
    0 ≤ e → Z.even b = false → Z.even (Zpower b e) = false := by
  intro he hb
  have hbOdd : Odd b := by
    rw [← Int.not_even_iff_odd, ← Z.even_spec]
    simpa using hb
  have hpNotEven : ¬ Even (b ^ e.toNat) := Int.not_even_iff_odd.mpr hbOdd.pow
  simpa [Zpower, he, ← Z.even_spec] using hpNotEven

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

/-- FLoCq `Zmod_mod_mult`. -/
@[flocq_source "src/Core/Zaux.v" 325 "Zmod_mod_mult"]
theorem Zmod_mod_mult (n a b : Int) (_ha : 0 < a) (_hb : 0 ≤ b) :
    n % (a * b) % b = n % b := by
  apply Int.emod_emod_of_dvd
  exact ⟨a, by ring⟩

/-- FLoCq `ZOmod_eq`. -/
@[flocq_source "src/Core/Zaux.v" 335 "ZOmod_eq"]
theorem ZOmod_eq (a b : Int) : a.tmod b = a - a.tdiv b * b := by
  simpa [Int.mul_comm] using Int.tmod_def a b

/-- FLoCq `Zdiv_mod_mult`. -/
@[flocq_source "src/Core/Zaux.v" 359 "Zdiv_mod_mult"]
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

/-- FLoCq `ZOmod_mod_mult`. -/
@[flocq_source "src/Core/Zaux.v" 344 "ZOmod_mod_mult"]
theorem ZOmod_mod_mult (n a b : Int) :
    (n.tmod (a * b)).tmod b = n.tmod b := by
  apply Int.tmod_tmod_of_dvd
  exact ⟨a, by ring⟩


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
@[flocq_source "src/Core/Zaux.v" 374 "ZOdiv_mod_mult"]
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

/-- Coq-compatible name: small-absolute-value truncated division is zero -/
@[flocq_source "src/Core/Zaux.v" 394 "ZOdiv_small_abs"]
theorem ZOdiv_small_abs (a b : Int) (h : (Int.natAbs a : Int) < b) :
    a.tdiv b = 0 := by
  by_cases ha : 0 ≤ a
  · exact Int.tdiv_eq_zero_of_lt ha (by simpa [Int.natAbs_of_nonneg ha] using h)
  · have hneg : 0 ≤ -a := neg_nonneg.mpr (le_of_not_ge ha)
    have habs : (Int.natAbs a : Int) = -a := by
      simpa [Int.natAbs_neg] using Int.natAbs_of_nonneg hneg
    have hz := Int.tdiv_eq_zero_of_lt hneg (by simpa [habs] using h)
    simpa [Int.neg_tdiv] using hz

/-- Coq-compatible name: small-absolute-value modulo is identity -/
@[flocq_source "src/Core/Zaux.v" 411 "ZOmod_small_abs"]
theorem ZOmod_small_abs (a b : Int) (h : (Int.natAbs a : Int) < b) :
    a.tmod b = a := by
  by_cases ha : 0 ≤ a
  · exact Int.tmod_eq_of_lt ha (by simpa [Int.natAbs_of_nonneg ha] using h)
  · have hneg : 0 ≤ -a := neg_nonneg.mpr (le_of_not_ge ha)
    have habs : (Int.natAbs a : Int) = -a := by
      simpa [Int.natAbs_neg] using Int.natAbs_of_nonneg hneg
    have hz := Int.tmod_eq_of_lt hneg (by simpa [habs] using h)
    simpa [Int.neg_tmod] using hz


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
@[flocq_source "src/Core/Zaux.v" 428 "ZOdiv_plus"]
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

/-- Coq-compatible name: transitivity of nonnegativity through a nonzero factor -/
@[flocq_source "src/Core/Zaux.v" 450 "Zsame_sign_trans"]
theorem Zsame_sign_trans (v u w : Int) (hv : v ≠ 0)
    (huv : 0 ≤ u * v) (hvw : 0 ≤ v * w) : 0 ≤ u * w := by
  rcases Int.mul_nonneg_iff.mp huv with ⟨hu, hv0⟩ | ⟨hu, hv0⟩ <;>
    rcases Int.mul_nonneg_iff.mp hvw with ⟨hv1, hw⟩ | ⟨hv1, hw⟩
  · exact mul_nonneg hu hw
  · exact (hv (le_antisymm hv1 hv0)).elim
  · exact (hv (le_antisymm hv0 hv1)).elim
  · exact mul_nonneg_of_nonpos_of_nonpos hu hw

/-- Coq-compatible name: weak transitivity of nonnegativity -/
@[flocq_source "src/Core/Zaux.v" 457 "Zsame_sign_trans_weak"]
theorem Zsame_sign_trans_weak (v u w : Int) (hzero : v = 0 → w = 0)
    (huv : 0 ≤ u * v) (hvw : 0 ≤ v * w) : 0 ≤ u * w := by
  by_cases hv : v = 0
  · simp [hzero hv]
  · exact Zsame_sign_trans v u w hv huv hvw

/-- Coq-compatible name: sign implications imply a nonnegative product. -/
@[flocq_source "src/Core/Zaux.v" 464 "Zsame_sign_imp"]
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

/-- Coq-compatible name: a nonnegative divisor gives a same-sign truncated quotient. -/
@[flocq_source "src/Core/Zaux.v" 483 "Zsame_sign_odiv"]
theorem Zsame_sign_odiv (u v : Int) (hv : 0 ≤ v) :
    0 ≤ u * Int.tdiv u v := by
  apply Zsame_sign_imp u (Int.tdiv u v)
  · intro hu
    exact Int.tdiv_nonneg (le_of_lt hu) hv
  · intro hu
    have h := Int.tdiv_nonneg (le_of_lt hu) hv
    simpa [Int.neg_tdiv] using h

end SameSign

/-! Boolean comparisons. Rocq's `Zeq_bool`, `Zle_bool` and `Zlt_bool` are Stdlib notations for
`Z.eqb`, `Z.leb` and `Z.ltb`; the port defines them as the Boolean decisions of the integer
relations, which compute and agree with Rocq on every input. -/

section Zeq_bool

/-- Boolean integer equality, Rocq's Stdlib `Zeq_bool` (a notation for `Z.eqb`). -/
@[flocq_local "Rocq Stdlib ZArith.Zbool.Zeq_bool, a notation for Z.eqb; not defined in Flocq itself"]
def Zeq_bool (x y : Int) : Bool :=
  decide (x = y)

/-- Graph of the integer equality test (FLoCq `Zeq_bool_prop`). -/
@[flocq_source "src/Core/Zaux.v" 502 "Zeq_bool_prop"]
inductive Zeq_bool_prop (x y : Int) : Bool → Prop where
  | Zeq_bool_true_ : x = y → Zeq_bool_prop x y true
  | Zeq_bool_false_ : x ≠ y → Zeq_bool_prop x y false

export Zeq_bool_prop (Zeq_bool_true_ Zeq_bool_false_)

/-- FLoCq `Zeq_bool_spec`: the graph of the Boolean equality test. -/
@[flocq_source "src/Core/Zaux.v" 506 "Zeq_bool_spec"]
theorem Zeq_bool_spec (x y : Int) : Zeq_bool_prop x y (Zeq_bool x y) := by
  by_cases h : x = y
  · simpa [Zeq_bool, h] using Zeq_bool_true_ (x := x) (y := y) h
  · simpa [Zeq_bool, h] using Zeq_bool_false_ (x := x) (y := y) h

/-- FLoCq `Zeq_bool_true`. -/
@[flocq_source "src/Core/Zaux.v" 518 "Zeq_bool_true"]
theorem Zeq_bool_true (x y : Int) (h : x = y) : Zeq_bool x y = true := by
  simp [Zeq_bool, h]

/-- FLoCq `Zeq_bool_false`. -/
@[flocq_source "src/Core/Zaux.v" 525 "Zeq_bool_false"]
theorem Zeq_bool_false (x y : Int) (h : x ≠ y) : Zeq_bool x y = false := by
  simp [Zeq_bool, h]

/-- FLoCq `Zeq_bool_diag`. -/
@[flocq_source "src/Core/Zaux.v" 537 "Zeq_bool_diag"]
theorem Zeq_bool_diag (x : Int) : Zeq_bool x x = true := by
  simp [Zeq_bool]

/-- FLoCq `Zeq_bool_opp`. -/
@[flocq_source "src/Core/Zaux.v" 544 "Zeq_bool_opp"]
theorem Zeq_bool_opp (x y : Int) : Zeq_bool (-x) y = Zeq_bool x (-y) := by
  by_cases h : -x = y <;> simp [Zeq_bool, h] <;> omega

/-- FLoCq `Zeq_bool_opp'`. -/
@[flocq_source "src/Core/Zaux.v" 561 "Zeq_bool_opp'"]
theorem Zeq_bool_opp' (x y : Int) : Zeq_bool (-x) (-y) = Zeq_bool x y := by
  simp [Zeq_bool]

end Zeq_bool

section Zle_bool

/-- Boolean integer order, Rocq's Stdlib `Zle_bool` (a notation for `Z.leb`). -/
@[flocq_local "Rocq Stdlib ZArith.Zbool.Zle_bool, a notation for Z.leb; not defined in Flocq itself"]
def Zle_bool (x y : Int) : Bool :=
  decide (x ≤ y)

/-- Graph of the integer less-or-equal test (FLoCq `Zle_bool_prop`). -/
@[flocq_source "src/Core/Zaux.v" 574 "Zle_bool_prop"]
inductive Zle_bool_prop (x y : Int) : Bool → Prop where
  | Zle_bool_true_ : x ≤ y → Zle_bool_prop x y true
  | Zle_bool_false_ : y < x → Zle_bool_prop x y false

export Zle_bool_prop (Zle_bool_true_ Zle_bool_false_)

/-- FLoCq `Zle_bool_spec`: the graph of the Boolean order test. -/
@[flocq_source "src/Core/Zaux.v" 578 "Zle_bool_spec"]
theorem Zle_bool_spec (x y : Int) : Zle_bool_prop x y (Zle_bool x y) := by
  by_cases h : x ≤ y
  · simpa [Zle_bool, h] using Zle_bool_true_ (x := x) (y := y) h
  · have hyx : y < x := lt_of_not_ge h
    simpa [Zle_bool, h] using Zle_bool_false_ (x := x) (y := y) hyx

/-- FLoCq `Zle_bool_true`. -/
@[flocq_source "src/Core/Zaux.v" 590 "Zle_bool_true"]
theorem Zle_bool_true (x y : Int) (h : x ≤ y) : Zle_bool x y = true := by
  simp [Zle_bool, h]

/-- FLoCq `Zle_bool_false`. -/
@[flocq_source "src/Core/Zaux.v" 598 "Zle_bool_false"]
theorem Zle_bool_false (x y : Int) (h : y < x) : Zle_bool x y = false := by
  simp [Zle_bool, Int.not_le.mpr h]

/-- FLoCq `Zle_bool_opp_l`. -/
@[flocq_source "src/Core/Zaux.v" 610 "Zle_bool_opp_l"]
theorem Zle_bool_opp_l (x y : Int) : Zle_bool (-x) y = Zle_bool (-y) x := by
  by_cases h : -x ≤ y <;> simp [Zle_bool, h] <;> omega

/-- FLoCq `Zle_bool_opp`. -/
@[flocq_source "src/Core/Zaux.v" 619 "Zle_bool_opp"]
theorem Zle_bool_opp (x y : Int) : Zle_bool (-x) (-y) = Zle_bool y x := by
  simp [Zle_bool]

/-- FLoCq `Zle_bool_opp_r`. -/
@[flocq_source "src/Core/Zaux.v" 627 "Zle_bool_opp_r"]
theorem Zle_bool_opp_r (x y : Int) : Zle_bool x (-y) = Zle_bool y (-x) := by
  by_cases h : x ≤ -y <;> simp [Zle_bool, h] <;> omega

end Zle_bool

section Zlt_bool

/-- Boolean strict integer order, Rocq's Stdlib `Zlt_bool` (a notation for `Z.ltb`). -/
@[flocq_local "Rocq Stdlib ZArith.Zbool.Zlt_bool, a notation for Z.ltb; not defined in Flocq itself"]
def Zlt_bool (x y : Int) : Bool :=
  decide (x < y)

/-- Graph of the integer strict-order test (FLoCq `Zlt_bool_prop`). -/
@[flocq_source "src/Core/Zaux.v" 640 "Zlt_bool_prop"]
inductive Zlt_bool_prop (x y : Int) : Bool → Prop where
  | Zlt_bool_true_ : x < y → Zlt_bool_prop x y true
  | Zlt_bool_false_ : y ≤ x → Zlt_bool_prop x y false

export Zlt_bool_prop (Zlt_bool_true_ Zlt_bool_false_)

/-- FLoCq `Zlt_bool_spec`: the graph of the Boolean strict-order test. -/
@[flocq_source "src/Core/Zaux.v" 644 "Zlt_bool_spec"]
theorem Zlt_bool_spec (x y : Int) : Zlt_bool_prop x y (Zlt_bool x y) := by
  by_cases h : x < y
  · simpa [Zlt_bool, h] using Zlt_bool_true_ (x := x) (y := y) h
  · have hyx : y ≤ x := le_of_not_gt h
    simpa [Zlt_bool, h] using Zlt_bool_false_ (x := x) (y := y) hyx

/-- FLoCq `Zlt_bool_true`. -/
@[flocq_source "src/Core/Zaux.v" 656 "Zlt_bool_true"]
theorem Zlt_bool_true (x y : Int) (h : x < y) : Zlt_bool x y = true := by
  simp [Zlt_bool, h]

/-- FLoCq `Zlt_bool_false`. -/
@[flocq_source "src/Core/Zaux.v" 664 "Zlt_bool_false"]
theorem Zlt_bool_false (x y : Int) (h : y ≤ x) : Zlt_bool x y = false := by
  simp [Zlt_bool, Int.not_lt.mpr h]

/-- FLoCq `negb_Zle_bool`. The parentheses matter: `!a = b` would parse as `!(a = b)`. -/
@[flocq_source "src/Core/Zaux.v" 676 "negb_Zle_bool"]
theorem negb_Zle_bool (x y : Int) : (!Zle_bool x y) = Zlt_bool y x := by
  simp only [Zle_bool, Zlt_bool, ← decide_not, Int.not_le]

/-- FLoCq `negb_Zlt_bool`. -/
@[flocq_source "src/Core/Zaux.v" 686 "negb_Zlt_bool"]
theorem negb_Zlt_bool (x y : Int) : (!Zlt_bool x y) = Zle_bool y x := by
  simp only [Zlt_bool, Zle_bool, ← decide_not, Int.not_lt]

/-- FLoCq `Zlt_bool_opp_l`. -/
@[flocq_source "src/Core/Zaux.v" 696 "Zlt_bool_opp_l"]
theorem Zlt_bool_opp_l (x y : Int) : Zlt_bool (-x) y = Zlt_bool (-y) x := by
  by_cases h : -x < y <;> simp [Zlt_bool, h] <;> omega

/-- FLoCq `Zlt_bool_opp_r`. -/
@[flocq_source "src/Core/Zaux.v" 705 "Zlt_bool_opp_r"]
theorem Zlt_bool_opp_r (x y : Int) : Zlt_bool x (-y) = Zlt_bool y (-x) := by
  by_cases h : x < -y <;> simp [Zlt_bool, h] <;> omega

/-- FLoCq `Zlt_bool_opp`. -/
@[flocq_source "src/Core/Zaux.v" 714 "Zlt_bool_opp"]
theorem Zlt_bool_opp (x y : Int) : Zlt_bool (-x) (-y) = Zlt_bool y x := by
  simp [Zlt_bool]

end Zlt_bool

section Zcompare

/-! Rocq's `comparison` is Lean's `Ordering` (constructors `Lt`/`Eq`/`Gt` are `.lt`/`.eq`/`.gt`),
and Rocq's `Z.compare` is Lean's `compare` on `Int`, so Flocq's `Zcompare_*` lemmas are stated
about `compare` directly. -/

/-- Graph of integer comparison (FLoCq `Zcompare_prop`). -/
@[flocq_source "src/Core/Zaux.v" 727 "Zcompare_prop"]
inductive Zcompare_prop (x y : Int) : Ordering → Prop where
  | Zcompare_Lt_ : x < y → Zcompare_prop x y .lt
  | Zcompare_Eq_ : x = y → Zcompare_prop x y .eq
  | Zcompare_Gt_ : y < x → Zcompare_prop x y .gt

export Zcompare_prop (Zcompare_Lt_ Zcompare_Eq_ Zcompare_Gt_)

/-- FLoCq `Zcompare_spec`: the graph of integer comparison. -/
@[flocq_source "src/Core/Zaux.v" 732 "Zcompare_spec"]
theorem Zcompare_spec (x y : Int) : Zcompare_prop x y (compare x y) := by
  rcases lt_trichotomy x y with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    exact Zcompare_Lt_ h
  · rw [compare_eq_iff_eq.mpr h]
    exact Zcompare_Eq_ h
  · rw [compare_gt_iff_gt.mpr h]
    exact Zcompare_Gt_ h

/-- FLoCq `Zcompare_Lt`. -/
@[flocq_source "src/Core/Zaux.v" 749 "Zcompare_Lt"]
theorem Zcompare_Lt (x y : Int) (h : x < y) : compare x y = Ordering.lt :=
  compare_lt_iff_lt.mpr h

/-- FLoCq `Zcompare_Eq`. -/
@[flocq_source "src/Core/Zaux.v" 756 "Zcompare_Eq"]
theorem Zcompare_Eq (x y : Int) (h : x = y) : compare x y = Ordering.eq :=
  compare_eq_iff_eq.mpr h

/-- FLoCq `Zcompare_Gt`. -/
@[flocq_source "src/Core/Zaux.v" 764 "Zcompare_Gt"]
theorem Zcompare_Gt (x y : Int) (h : y < x) : compare x y = Ordering.gt :=
  compare_gt_iff_gt.mpr h

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

/-- FLoCq `cond_Zopp_0`. -/
@[flocq_source "src/Core/Zaux.v" 776 "cond_Zopp_0"]
theorem cond_Zopp_0 (sx : Bool) : cond_Zopp sx 0 = 0 := by
  cases sx <;> rfl

/-- FLoCq `cond_Zopp_negb`. -/
@[flocq_source "src/Core/Zaux.v" 782 "cond_Zopp_negb"]
theorem cond_Zopp_negb (x : Bool) (y : Int) :
    cond_Zopp (!x) y = -cond_Zopp x y := by
  cases x <;> simp [cond_Zopp]

/-- FLoCq `abs_cond_Zopp`. -/
@[flocq_source "src/Core/Zaux.v" 790 "abs_cond_Zopp"]
theorem abs_cond_Zopp (b : Bool) (m : Int) :
    |cond_Zopp b m| = |m| := by
  cases b <;> simp [cond_Zopp]

/-- FLoCq `cond_Zopp_Zlt_bool`. -/
@[flocq_source "src/Core/Zaux.v" 799 "cond_Zopp_Zlt_bool"]
theorem cond_Zopp_Zlt_bool (m : Int) :
    cond_Zopp (Zlt_bool m 0) m = |m| := by
  by_cases h : m < 0
  · simp [cond_Zopp, Zlt_bool, h, abs_of_nonpos h.le]
  · simp [cond_Zopp, Zlt_bool, h, abs_of_nonneg (le_of_not_gt h)]

/-- FLoCq `Zeq_bool_cond_Zopp`. -/
@[flocq_source "src/Core/Zaux.v" 811 "Zeq_bool_cond_Zopp"]
theorem Zeq_bool_cond_Zopp (s : Bool) (m n : Int) :
    Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n) := by
  cases s
  · rfl
  · exact Zeq_bool_opp m n

end CondZopp

section FastPower

/-- Fast exponentiation for positive exponents, by repeated squaring along the binary digits
of the exponent: FLoCq's `Zfast_pow_pos`, with Rocq's `Z.square x` written `x ^ 2`. -/
@[flocq_source "src/Core/Zaux.v" 824 "Zfast_pow_pos"]
def Zfast_pow_pos (v : Int) (e : Positive) : Int :=
  match e with
  | .xH => v
  | .xO e' => Zfast_pow_pos v e' ^ 2
  | .xI e' => v * Zfast_pow_pos v e' ^ 2

/-- FLoCq `Zfast_pow_pos_correct`: repeated squaring computes the positive power. -/
@[flocq_source "src/Core/Zaux.v" 831 "Zfast_pow_pos_correct"]
theorem Zfast_pow_pos_correct (v : Int) (e : Positive) :
    Zfast_pow_pos v e = Zpower_pos v e := by
  induction e with
  | xH => simp [Zfast_pow_pos, Zpower_pos, positiveToNat]
  | xO e ih =>
      simp only [Zfast_pow_pos, ih, Zpower_pos, positiveToNat]
      ring
  | xI e ih =>
      simp only [Zfast_pow_pos, ih, Zpower_pos, positiveToNat]
      ring

end FastPower

section FasterDiv

/-- Coq `Z.div_eucl`: floor quotient and a remainder with the divisor's sign. -/
@[flocq_local "Rocq Stdlib Z.div_eucl, the floor quotient/remainder pair; not defined in Flocq itself"]
def Z_div_eucl (a b : Int) : (Int × Int) :=
  let q := Int.fdiv a b
  (q, a - b * q)

/-- FLoCq `Zdiv_eucl_unique`, with Rocq's floor `Z.div`/`Z.modulo` as `Int.fdiv`/`Int.fmod`. -/
@[flocq_source "src/Core/Zaux.v" 853 "Zdiv_eucl_unique"]
theorem Zdiv_eucl_unique (a b : Int) :
    Z_div_eucl a b = (Int.fdiv a b, Int.fmod a b) := by
  simp [Z_div_eucl, Int.fmod_def]

/-- Coq `Zpos`: embed a positive integer into `Int`. -/
@[flocq_local "Rocq Corelib BinNums.Zpos, the positive constructor of Z, as a function into Int"]
def Zpos (p : Positive) : Int :=
  positiveToNat p

theorem Zpos_pos (p : Positive) : 0 < Zpos p := by
  simpa [Zpos] using positiveToNat_pos p

/-- The positive with value `n` (`xH` for `0`), built from its binary digits. The first
argument is fuel: `n` itself suffices, and only about `log₂ n` steps are taken. -/
private def Pos_of_nat_aux : Nat → Nat → Positive
  | 0, _ => .xH
  | fuel + 1, n =>
      if n ≤ 1 then .xH
      else if n % 2 = 0 then .xO (Pos_of_nat_aux fuel (n / 2))
      else .xI (Pos_of_nat_aux fuel (n / 2))

/-- Rocq's `Pos.of_nat`: the positive with value `n`, and `xH` for `0`. -/
@[flocq_local "Rocq Stdlib PArith Pos.of_nat; not defined in Flocq itself"]
def Pos_of_nat (n : Nat) : Positive :=
  Pos_of_nat_aux n n

private theorem Pos_of_nat_aux_spec :
    ∀ fuel n, 0 < n → n ≤ fuel → positiveToNat (Pos_of_nat_aux fuel n) = n
  | 0, n, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
      unfold Pos_of_nat_aux
      by_cases h1 : n ≤ 1
      · simp only [h1, ↓reduceIte, positiveToNat]
        omega
      · have ih := Pos_of_nat_aux_spec fuel (n / 2) (by omega) (by omega)
        by_cases h2 : n % 2 = 0
        · simp only [h1, h2, ↓reduceIte, positiveToNat, ih]
          omega
        · simp only [h1, h2, ↓reduceIte, positiveToNat, ih]
          omega

theorem Pos_of_nat_spec (n : Nat) (hn : 0 < n) : positiveToNat (Pos_of_nat n) = n :=
  Pos_of_nat_aux_spec n n hn le_rfl

/-- Rocq's three constructors of `Z`: `Z0`, `Zpos p` and `Zneg p`. -/
@[flocq_local "View of Int through Rocq's Z constructors Z0/Zpos/Zneg, for literal ports of Rocq matches"]
inductive ZView where
  | Z0 : ZView
  | Zpos : Positive → ZView
  | Zneg : Positive → ZView

/-- Decompose an integer as Rocq's `Z` constructors would. -/
@[flocq_local "View of Int through Rocq's Z constructors Z0/Zpos/Zneg, for literal ports of Rocq matches"]
def zview : Int → ZView
  | .ofNat 0 => .Z0
  | .ofNat (n + 1) => .Zpos (Pos_of_nat (n + 1))
  | .negSucc n => .Zneg (Pos_of_nat (n + 1))

/-- Rocq's `Pos.compare`, the order of the values. -/
@[flocq_local "Rocq Stdlib PArith Pos.compare; not defined in Flocq itself"]
def Pos_compare (a b : Positive) : Ordering :=
  compare (positiveToNat a) (positiveToNat b)

/-- Coq `Z.pos_div_eucl a b`, which Flocq applies only to positive divisors `b`. On that
domain it is the Euclidean (equivalently, floor) quotient and remainder. -/
@[flocq_local "Rocq Stdlib Z.pos_div_eucl, on the positive divisors Flocq uses; not defined in Flocq itself"]
def Z_pos_div_eucl (a : Positive) (b : Int) : Int × Int :=
  (Zpos a / b, Zpos a % b)

/-- A quotient/remainder pair is the Euclidean one when it decomposes the dividend with an
in-range remainder. -/
private theorem pair_eq_ediv_emod {n d q r : Int} (hd : 0 < d)
    (h : r + d * q = n) (h0 : 0 ≤ r) (hr : r < d) : (q, r) = (n / d, n % d) := by
  obtain ⟨h1, h2⟩ := (Int.ediv_emod_unique hd).mpr ⟨h, h0, hr⟩
  rw [h1, h2]

/-- FLoCq `Zpos_div_eucl_aux1`: Euclidean division of positives, peeling the common
trailing zero digits of an even divisor and falling back to `Z.pos_div_eucl` at an odd one. -/
@[flocq_source "src/Core/Zaux.v" 862 "Zpos_div_eucl_aux1"]
def Zpos_div_eucl_aux1 (a b : Positive) : Int × Int :=
  match b with
  | .xO b' =>
    match a with
    | .xO a' => let (q, r) := Zpos_div_eucl_aux1 a' b'; (q, 2 * r)
    | .xI a' => let (q, r) := Zpos_div_eucl_aux1 a' b'; (q, 2 * r + 1)
    | .xH => (0, Zpos a)
  | .xH => (Zpos a, 0)
  | .xI _ => Z_pos_div_eucl a (Zpos b)
termination_by structural b

/-- FLoCq `Zpos_div_eucl_aux1_correct`. -/
@[flocq_source "src/Core/Zaux.v" 874 "Zpos_div_eucl_aux1_correct"]
theorem Zpos_div_eucl_aux1_correct (a b : Positive) :
    Zpos_div_eucl_aux1 a b = Z_pos_div_eucl a (Zpos b) := by
  induction b generalizing a with
  | xH => simp [Zpos_div_eucl_aux1, Z_pos_div_eucl, Zpos, positiveToNat]
  | xI b => rfl
  | xO b ih =>
      have hB := Zpos_pos b
      have hb : Zpos (.xO b) = 2 * Zpos b := by simp [Zpos, positiveToNat]
      cases a with
      | xH =>
          simp only [Zpos_div_eucl_aux1, Z_pos_div_eucl, hb]
          have h1 : Zpos .xH = 1 := by simp [Zpos, positiveToNat]
          exact pair_eq_ediv_emod (by omega) (by omega) (by omega) (by omega)
      | xO a =>
          have ha : Zpos (.xO a) = 2 * Zpos a := by simp [Zpos, positiveToNat]
          have hq := Int.emod_add_mul_ediv (Zpos a) (Zpos b)
          have h0 := Int.emod_nonneg (Zpos a) (Int.ne_of_gt hB)
          have hr := Int.emod_lt_of_pos (Zpos a) hB
          simp only [Zpos_div_eucl_aux1, ih, Z_pos_div_eucl, ha, hb]
          exact pair_eq_ediv_emod (by omega) (by linear_combination 2 * hq) (by omega) (by omega)
      | xI a =>
          have ha : Zpos (.xI a) = 2 * Zpos a + 1 := by simp [Zpos, positiveToNat]
          have hq := Int.emod_add_mul_ediv (Zpos a) (Zpos b)
          have h0 := Int.emod_nonneg (Zpos a) (Int.ne_of_gt hB)
          have hr := Int.emod_lt_of_pos (Zpos a) hB
          simp only [Zpos_div_eucl_aux1, ih, Z_pos_div_eucl, ha, hb]
          exact pair_eq_ediv_emod (by omega) (by linear_combination 2 * hq) (by omega) (by omega)

/-- FLoCq `Zpos_div_eucl_aux`: settle `a ≤ b` by comparison before dividing. -/
@[flocq_source "src/Core/Zaux.v" 913 "Zpos_div_eucl_aux"]
def Zpos_div_eucl_aux (a b : Positive) : Int × Int :=
  match Pos_compare a b with
  | .lt => (0, Zpos a)
  | .eq => (1, 0)
  | .gt => Zpos_div_eucl_aux1 a b

/-- FLoCq `Zpos_div_eucl_aux_correct`. -/
@[flocq_source "src/Core/Zaux.v" 920 "Zpos_div_eucl_aux_correct"]
theorem Zpos_div_eucl_aux_correct (a b : Positive) :
    Zpos_div_eucl_aux a b = Z_pos_div_eucl a (Zpos b) := by
  have hA := Zpos_pos a
  have hB := Zpos_pos b
  unfold Zpos_div_eucl_aux Pos_compare
  rcases lt_trichotomy (positiveToNat a) (positiveToNat b) with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    have h' : Zpos a < Zpos b := by simpa [Zpos] using h
    exact pair_eq_ediv_emod hB (by ring) hA.le h'
  · rw [compare_eq_iff_eq.mpr h]
    have h' : Zpos a = Zpos b := by simp [Zpos, h]
    exact pair_eq_ediv_emod hB (by rw [h']; ring) le_rfl hB
  · rw [compare_gt_iff_gt.mpr h]
    exact Zpos_div_eucl_aux1_correct a b

/-- FLoCq `Zfast_div_eucl`: Rocq's `Z.div_eucl`, computed by sign cases from the Euclidean
division of the absolute values. The zero-divisor branch tests `1 mod 0` as the source does,
so that it follows whichever convention `Z.modulo` has for zero; in Rocq 9.1 and in Lean
(`Int.fmod 1 0 = 1`), division by zero returns `(0, a)`. -/
@[flocq_source "src/Core/Zaux.v" 936 "Zfast_div_eucl"]
def Zfast_div_eucl (a b : Int) : Int × Int :=
  match zview a with
  | .Z0 => (0, 0)
  | .Zpos a' =>
    match zview b with
    | .Z0 => (0, match Int.fmod 1 0 with | 0 => 0 | _ => a)
    | .Zpos b' => Zpos_div_eucl_aux a' b'
    | .Zneg b' =>
      let (q, r) := Zpos_div_eucl_aux a' b'
      match zview r with
      | .Z0 => (-q, 0)
      | .Zpos _ => (-(q + 1), b + r)
      | .Zneg _ => (-(q + 1), b + r)
  | .Zneg a' =>
    match zview b with
    | .Z0 => (0, match Int.fmod 1 0 with | 0 => 0 | _ => a)
    | .Zpos b' =>
      let (q, r) := Zpos_div_eucl_aux a' b'
      match zview r with
      | .Z0 => (-q, 0)
      | .Zpos _ => (-(q + 1), b - r)
      | .Zneg _ => (-(q + 1), b - r)
    | .Zneg b' => let (q, r) := Zpos_div_eucl_aux a' b'; (q, -r)

/-- The floor pair for a positive divisor, from a decomposition with remainder in `[0, b)`. -/
private theorem pair_eq_floor_pos {a b q r : Int} (hb : 0 < b)
    (h : r + b * q = a) (h0 : 0 ≤ r) (hr : r < b) : (q, r) = Z_div_eucl a b := by
  obtain ⟨h1, h2⟩ := (Int.fdiv_fmod_unique hb).mpr ⟨h, h0, hr⟩
  rw [Zdiv_eucl_unique, h1, h2]

/-- The floor pair for a negative divisor, from a decomposition with remainder in `(b, 0]`. -/
private theorem pair_eq_floor_neg {a b q r : Int} (hb : b < 0)
    (h : r + b * q = a) (h0 : b < r) (hr : r ≤ 0) : (q, r) = Z_div_eucl a b := by
  obtain ⟨h1, h2⟩ := (Int.fdiv_fmod_unique' hb).mpr ⟨h, h0, hr⟩
  rw [Zdiv_eucl_unique, h1, h2]

private theorem zview_zero : zview 0 = .Z0 := rfl

private theorem zview_succ (k : Nat) : zview ((k + 1 : Nat) : Int) = .Zpos (Pos_of_nat (k + 1)) :=
  rfl

/-- Every integer is Rocq's `Z0`, `Zpos p` or `Zneg p`, and `zview` reports which. -/
theorem zview_cases (z : Int) :
    (z = 0 ∧ zview z = .Z0) ∨ (∃ p, z = Zpos p ∧ zview z = .Zpos p) ∨
      (∃ p, z = -Zpos p ∧ zview z = .Zneg p) := by
  rcases z with (_ | k) | k
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr (Or.inl ⟨Pos_of_nat (k + 1), ?_, rfl⟩)
    simp [Zpos, Pos_of_nat_spec]
  · refine Or.inr (Or.inr ⟨Pos_of_nat (k + 1), ?_, rfl⟩)
    simp [Zpos, Pos_of_nat_spec, Int.negSucc_eq]

/-- A remainder of a positive divisor is zero or the value of a positive. -/
private theorem emod_zero_or_succ (A B : Int) (hB : 0 < B) :
    A % B = 0 ∨ ∃ k : Nat, A % B = ((k + 1 : Nat) : Int) := by
  have h0 := Int.emod_nonneg A (Int.ne_of_gt hB)
  by_cases h : A % B = 0
  · exact Or.inl h
  · exact Or.inr ⟨(A % B).toNat - 1, by omega⟩

/-- FLoCq `Zfast_div_eucl_correct`: the fast algorithm computes `Z.div_eucl`. -/
@[flocq_source "src/Core/Zaux.v" 965 "Zfast_div_eucl_correct"]
theorem Zfast_div_eucl_correct (a b : Int) :
    Zfast_div_eucl a b = Z_div_eucl a b := by
  have h10 : Int.fmod 1 0 = 1 := by decide
  rcases zview_cases a with ⟨rfl, ha⟩ | ⟨a', rfl, ha⟩ | ⟨a', rfl, ha⟩ <;>
    rcases zview_cases b with ⟨rfl, hb⟩ | ⟨b', rfl, hb⟩ | ⟨b', rfl, hb⟩ <;>
    simp only [Zfast_div_eucl, ha, hb, h10, Zpos_div_eucl_aux_correct, Z_pos_div_eucl]
  -- A zero dividend or divisor.
  all_goals first
    | (simp [Z_div_eucl]; done)
    | skip
  -- Signs: the source corrects the Euclidean division of the absolute values.
  all_goals
    have hB := Zpos_pos b'
    have hq := Int.emod_add_mul_ediv (Zpos a') (Zpos b')
    have h0 := Int.emod_nonneg (Zpos a') (Int.ne_of_gt hB)
    have hr := Int.emod_lt_of_pos (Zpos a') hB
  · exact pair_eq_floor_pos hB hq h0 hr
  · rcases emod_zero_or_succ (Zpos a') (Zpos b') hB with h | ⟨k, h⟩ <;> rw [h]
    · rw [zview_zero]
      exact pair_eq_floor_neg (by omega) (by linear_combination hq - h) (by omega) le_rfl
    · rw [zview_succ]
      exact pair_eq_floor_neg (by omega) (by linear_combination hq - h) (by omega) (by omega)
  · rcases emod_zero_or_succ (Zpos a') (Zpos b') hB with h | ⟨k, h⟩ <;> rw [h]
    · rw [zview_zero]
      exact pair_eq_floor_pos hB (by linear_combination -hq + h) le_rfl hB
    · rw [zview_succ]
      exact pair_eq_floor_pos hB (by linear_combination -hq + h) (by omega) (by omega)
  · exact pair_eq_floor_neg (by omega) (by linear_combination -hq) (by omega) (by omega)

end FasterDiv

section Iteration

/-- FLoCq `iter_nat`: apply `f` to `x` a total of `n` times. As in the source, each step
applies `f` first and recurses on the result (`iter_nat n' (f x)`), the same unfolding as
`Function.iterate`; `iter_nat_S` gives the step that applies `f` last. -/
@[flocq_source "src/Core/Zaux.v" 980 "iter_nat"]
def iter_nat {A : Type} (f : A → A) (n : Nat) (x : A) : A :=
  match n with
  | n' + 1 => iter_nat f n' (f x)
  | 0 => x

/-- Specification: Iteration applies function n times. -/
theorem iter_nat_spec {A : Type} (f : A → A) (n : Nat) (x : A) :
    iter_nat f n x = f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-- FLoCq `iter_nat_plus`. -/
@[flocq_source "src/Core/Zaux.v" 986 "iter_nat_plus"]
theorem iter_nat_plus {A : Type} (f : A → A) (p q : Nat) (x : A) :
    iter_nat f (p + q) x = iter_nat f p (iter_nat f q x) := by
  induction q generalizing x with
  | zero => rfl
  | succ q ih => exact ih (f x)

/-- FLoCq `iter_nat_S`. -/
@[flocq_source "src/Core/Zaux.v" 997 "iter_nat_S"]
theorem iter_nat_S {A : Type} (f : A → A) (p : Nat) (x : A) :
    iter_nat f (p + 1) x = f (iter_nat f p x) := by
  induction p generalizing x with
  | zero => rfl
  | succ p ih => exact ih (f x)

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
    iter_nat f n (f x) = f (iter_nat f n x) :=
  iter_nat_S f n x

/-- FLoCq `iter_pos_nat`: binary-positive iteration agrees with natural-count iteration. -/
@[flocq_source "src/Core/Zaux.v" 1008 "iter_pos_nat"]
theorem iter_pos_nat {A : Type} (f : A → A) (p : Positive) (x : A) :
    iter_pos f p x = iter_nat f (positiveToNat p) x := by
  induction p generalizing x with
  | xH => rfl
  | xO p ih =>
      simp only [iter_pos, positiveToNat, ih, ← iter_nat_plus, two_mul]
  | xI p ih =>
      simp only [iter_pos, positiveToNat, ih, ← iter_nat_plus, two_mul,
        iter_nat_S, iter_nat_apply]

end Iteration

end FloatSpec.Core.Zaux
