import FloatSpec.src.Core.Raux

/-! Source-shaped LPO consumers. These are classical proof-carrying alternatives,
not native decision procedures for arbitrary predicates. -/

namespace FloatSpec.Test.LpoSourceContracts

open FloatSpec.Core.Raux

/-- Consume the exact minimal natural-witness result shape. -/
noncomputable def minClient (P : Nat → Prop) (hdec : ∀ n, P n ∨ ¬ P n) :
    PSum {n : Nat // P n ∧ ∀ i : Nat, i < n → ¬ P i} (∀ n : Nat, ¬ P n) :=
  LPO_min P hdec

/-- Consume the exact natural-witness result shape. -/
noncomputable def natClient (P : Nat → Prop) (hdec : ∀ n, P n ∨ ¬ P n) :
    PSum {n : Nat // P n} (∀ n : Nat, ¬ P n) := LPO P hdec

/-- Consume the exact integer-witness result shape. -/
noncomputable def intClient (P : Int → Prop) (hdec : ∀ n, P n ∨ ¬ P n) :
    PSum {n : Int // P n} (∀ n : Int, ¬ P n) := LPO_Z P hdec

/-- Erasing the carried proof preserves the former minimal optional choice. -/
theorem min_choice_projection (P : Nat → Prop) (hdec : ∀ n, P n ∨ ¬ P n) :
    (match LPO_min P hdec with | .inl witness => some witness.val | .inr _ => none) =
      LPO_min_choice P := by
  classical
  by_cases h : ∃ n, P n <;> simp [LPO_min, LPO_min_choice, h]

/-- Erasing a natural witness preserves the former optional natural choice. -/
theorem nat_choice_projection (P : Nat → Prop) (hdec : ∀ n, P n ∨ ¬ P n) :
    (match LPO P hdec with | .inl witness => some witness.val | .inr _ => none) =
      LPO_choice P := by
  classical
  by_cases h : ∃ n, P n <;> simp [LPO, LPO_min, LPO_choice, h]

/-- A source-shaped consumer extracts data using the carried membership proof. -/
noncomputable def naturalWitness (P : Nat → Prop) (hdec : ∀ n, P n ∨ ¬ P n)
    (hex : ∃ n, P n) : {n : Nat // P n} :=
  match natClient P hdec with
  | .inl witness => witness
  | .inr noWitness => False.elim (hex.elim (fun n hn => noWitness n hn))

/-- The integer consumer needs no separate specification theorem. -/
noncomputable def integerWitness (P : Int → Prop) (hdec : ∀ n, P n ∨ ¬ P n)
    (hex : ∃ n, P n) : {n : Int // P n} :=
  match intClient P hdec with
  | .inl witness => witness
  | .inr noWitness => False.elim (hex.elim (fun n hn => noWitness n hn))

/-- A negative-only witness remains available through the source-shaped type. -/
theorem negative_witness (hdec : ∀ n : Int, n = -3 ∨ n ≠ -3) :
    (integerWitness (fun n => n = -3) hdec ⟨-3, rfl⟩).val = -3 :=
  (integerWitness (fun n => n = -3) hdec ⟨-3, rfl⟩).property

/-- The impossible positive branch carries enough evidence to eliminate itself. -/
theorem empty_predicate (hdec : ∀ _n : Nat, False ∨ ¬ False) :
    match natClient (fun _ => False) hdec with
    | .inl _ => False
    | .inr _ => True := by
  cases natClient (fun _ => False) hdec with
  | inl witness => exact witness.property
  | inr _ => trivial

#print axioms minClient
#print axioms natClient
#print axioms intClient
#print axioms min_choice_projection
#print axioms nat_choice_projection
#print axioms negative_witness
#print axioms empty_predicate

end FloatSpec.Test.LpoSourceContracts
