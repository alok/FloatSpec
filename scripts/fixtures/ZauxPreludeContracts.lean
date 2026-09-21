import FloatSpec.src.Version
import FloatSpec.src.Core.Zaux

/-! First source-ordered slice: pinned version metadata, imported aliases,
integer propositions and Boolean proof infrastructure. Paired with Rocq. -/

namespace ZauxPreludeContracts
open FloatSpec.Core.Zaux

example : Flocq_version.Flocq_version = 40202 := rfl
example : ∀ x y : Int, -y ≤ -x → x ≤ y := Zopp_le_cancel
example : ∀ x y : Int, y < x → x ≠ y := Zgt_not_eq
example (P : Bool → Sort u) (h : P true) : eqbool_dep P h true = (fun h' => h = h') := rfl
example (P : Bool → Sort u) (h : P true) : eqbool_dep P h false = (fun _ => False) := rfl
example : ∀ (b : Bool) (h₁ h₂ : b = true), h₁ = h₂ := eqbool_irrelevance
example (b : Bool) (x : Int) : cond_Zopp b x = if b then -x else x := rfl

-- The exact binary-recursive body imported by Flocq from Corelib.SpecFloat.
private def sourceIter {A : Type} (f : A → A) : Positive → A → A
  | .xH, x => f x
  | .xO p, x => sourceIter f p (sourceIter f p x)
  | .xI p, x => sourceIter f p (sourceIter f p (f x))

private theorem iter_nat_apply {A : Type} (f : A → A) (n : Nat) (x : A) :
    iter_nat f n (f x) = f (iter_nat f n x) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [iter_nat] using congrArg f ih

private theorem sourceIter_eq_iter_nat {A : Type} (f : A → A) (p : Positive) (x : A) :
    sourceIter f p x = iter_nat f (positiveToNat p) x := by
  induction p generalizing x with
  | xH => rfl
  | xO p ih =>
      simp only [sourceIter, positiveToNat, ih, ← iter_nat_plus, two_mul]
  | xI p ih =>
      simp only [sourceIter, positiveToNat, ih, ← iter_nat_plus, two_mul,
        iter_nat_S, iter_nat_apply]

#print axioms sourceIter_eq_iter_nat

example {A : Type} (f : A → A) (p : Positive) (x : A) :
    sourceIter f p x = iter_pos f p x :=
  (sourceIter_eq_iter_nat f p x).trans (iter_pos_nat f p x).symm

#print axioms iter_pos_nat

private def positives : List Positive :=
  [.xH, .xO .xH, .xI .xH, .xO (.xO .xH), .xI (.xO .xH),
   .xO (.xI .xH), .xI (.xI .xH), .xO (.xO (.xO .xH))]

-- A changing state makes iteration counts observable; identity would not.
private def observe : List Int :=
  positives.map (fun p => iter_pos (fun x : Int => 2 * x + 3) p (-2))

example : observe = [-1, 1, 5, 13, 29, 61, 125, 253] := by decide +kernel

#eval do
  unless observe == [-1, 1, 5, 13, 29, 61, 125, 253] do
    throw (IO.userError "source positive-iteration regression")
  for b in [false, true] do
    for x in [-1000000, -7, -1, 0, 1, 7, 1000000] do
      unless cond_Zopp b x == (if b then -x else x) do
        throw (IO.userError "conditional negation regression")
  IO.println "PASS: pinned version, exact prelude contracts, 8 binary iterations, 14 sign cases"

end ZauxPreludeContracts
