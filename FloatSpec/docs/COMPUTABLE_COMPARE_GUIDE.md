# Building the computable comparison backend, by hand

A guide to implementing `FloatSpec/src/IEEE754/ComputableCompare.lean` yourself,
from the surrounding system outward. Written so you could delete the module and
rebuild it without looking.

---

## 0. The bug, in one screenful

```lean
$ cat > /tmp/x.lean <<'EOF'
import FloatSpec.src.IEEE754.PrimFloat
def a : StandardFloat := StandardFloat.S754_finite false 3 (-1)   -- 1.5
def b : StandardFloat := StandardFloat.S754_finite false 6 (-2)   -- also 1.5
#eval FaithfulPrimFloat.SFeqb a b
EOF
$ lake env lean /tmp/x.lean
error: failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'FaithfulPrimFloat.SFeqb', which is 'noncomputable'
```

`SFeqb : StandardFloat → StandardFloat → Bool`. Both arguments are finite
bit-pattern encodings. The return type is `Bool`. And yet it cannot run.

That is not a performance problem or a missing `@[inline]`. Lean is telling you
the function has **no compiled code at all**, because somewhere inside it, a
decision was made by an oracle rather than by an algorithm.

This matters beyond aesthetics. The FloatLib paper (arXiv 2609.19352, Sept 2026)
cites FloatSpec and distinguishes itself on exactly this: FloatSpec has
"noncomputable rounded IEEE interfaces," while FloatLib "carries the rounded
encoded specification through executable backend selection." They were right.
This module makes that sentence false for the comparison API.

---

## 1. Background you need

### 1.1 What `noncomputable` actually means in Lean 4

Lean's kernel is a dependent type theory; its *logic* is classical, but its
*compiler* only emits code for definitions built from constructors, recursors,
and other compiled definitions. The instant a definition's value depends on
something with no algorithm — the axiom of choice, `Classical.em`, arbitrary
real-number equality — Lean refuses to emit code and demands the
`noncomputable` marker.

`noncomputable` is therefore not a warning you can silence. It is a factual
claim: *this definition names a mathematical object, and cannot be executed.*

### 1.2 Why real numbers are the usual culprit

In Mathlib, `ℝ` is Cauchy sequences of rationals quotiented by an equivalence
relation. Equality of two reals is **not decidable** — there is no algorithm
that, given two arbitrary reals, terminates with yes or no. (Consider a real
defined as "1 if the Collatz conjecture holds, 0 otherwise.")

So `DecidableEq ℝ` has no honest instance. Any `decide (x = y)` for `x y : ℝ`
must come from somewhere else.

### 1.3 The trap: `open Classical`

`PrimFloat.lean` line 12 says:

```lean
open Classical
```

In Mathlib, `Classical.propDecidable` is a `scoped instance` with low priority:

```lean
scoped instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨Decidable.isTrue h⟩
    | Or.inr h => ⟨Decidable.isFalse h⟩
```

`open Classical` brings it into scope. Now **every** proposition is `Decidable`,
so `decide p` typechecks for any `p` whatsoever — including `x = y` for reals.
It elaborates cleanly. No error, no warning. The only symptom is that the
definition silently becomes `noncomputable`, and so does everything downstream.

This is the single most important thing to internalize: **`open Classical` turns
a type error into a silent loss of executability.** Without it, `decide (SF2R 2 x
= SF2R 2 y)` would have been a "failed to synthesize `Decidable`" error at the
exact line of the mistake, and nobody would have shipped it.

### 1.4 Why a *port* is especially vulnerable

FloatSpec is a port of Coq's Flocq. Flocq defines comparison mathematically:

```coq
Definition SFeqb (x y : spec_float) : bool := ...  (* compares via R *)
```

In Coq this is fine, because Coq's reals are axiomatized classically and nobody
expects `SFeqb` to compute either. Translating the definition *literally* is the
faithful thing to do — and `@[flocq_source]` annotations in this repo exist
precisely to enforce literal correspondence.

The failure mode is that faithfulness to a specification and executability pull
in opposite directions. The fix is not to abandon faithfulness. It is to have
**both artifacts and a proof that they agree** — which is the pattern below.

---

## 2. The surrounding system

### 2.1 `StandardFloat`

`FloatSpec/src/IEEE754/Binary.lean:35`:

```lean
inductive StandardFloat where
  | S754_zero (s : Bool) : StandardFloat
  | S754_infinity (s : Bool) : StandardFloat
  | S754_nan : StandardFloat
  | S754_finite (s : Bool) (m : Nat) (e : Int) : StandardFloat
deriving DecidableEq
```

This is Flocq's `spec_float`: the IEEE 754 *interchange* view. Note it already
`deriving DecidableEq` — structural equality computes fine. What does not
compute is **value** equality, which is a different relation: `S754_finite false
3 (-1)` and `S754_finite false 6 (-2)` are structurally distinct but both denote
1.5.

### 2.2 `F2R` and `SF2R` — the meaning function

`FloatSpec/src/Core/Defs.lean:94`:

```lean
noncomputable def F2R (f : FlocqFloat beta) : ℝ :=
  (f.Fnum * (beta : ℝ) ^ f.Fexp)
```

`FlocqFloat beta` is a record `⟨Fnum : Int, Fexp : Int⟩`. `F2R` says: the pair
`(n, e)` means the real `n · β^e`. This one *should* be noncomputable — its
codomain is `ℝ`. That is honest.

`Binary.lean:58` lifts it:

```lean
noncomputable def SF2R (beta : Int) [ValidRadix beta] (x : StandardFloat) : ℝ :=
  match x with
  | StandardFloat.S754_finite s m e =>
    F2R (FlocqFloat.mk (if s then -(m : Int) else (m : Int)) e)
  | _ => 0
```

Zero, infinity, and NaN all map to `0`. (Infinity and NaN have no real value;
Flocq maps them to 0 and handles them by case analysis *before* ever calling
`SF2R`. Keep that in mind — it is why the fallthrough arm below is safe.)

### 2.3 The three lemmas that make this work

All in `FloatSpec/src/Core/Float_prop.lean`. These already existed; the whole
contribution is noticing they compose.

```lean
theorem F2R_change_exp (f : FlocqFloat beta) (e' : Int) (hbeta : 1 < beta)
    (he : e' ≤ f.Fexp) :
    F2R f = F2R (FlocqFloat.mk (f.Fnum * beta ^ (f.Fexp - e').natAbs) e')
```
*Rescaling to a smaller exponent preserves the value.* `n · β^e = (n · β^(e−e')) · β^e'`.

```lean
theorem lt_F2R_iff (e m1 m2 : Int) (hbeta : 1 < beta) :
    m1 < m2 ↔ F2R (FlocqFloat.mk m1 e) < F2R (FlocqFloat.mk m2 e)
```
*At a **common** exponent, real order is exactly integer order on mantissas.*
True because `β^e > 0`, so multiplying by it is strictly monotone.

```lean
theorem eq_F2R (e m1 m2 : Int) :
    F2R (FlocqFloat.mk m1 e) = F2R (FlocqFloat.mk m2 e) → m1 = m2
```
*Same, for equality* (cancel the nonzero factor `β^e`).

**The whole proof strategy falls out of these.** `change_exp` gets you to a
common exponent; `lt_F2R_iff`/`eq_F2R` then reduce a real comparison to an
integer comparison. Integers are decidable. Done.

---

## 3. The mathematical idea

A finite `StandardFloat` denotes a **dyadic rational**: `(−1)^s · m · 2^e` with
`m : ℕ`, `e : ℤ`. Dyadics are a subring of ℚ, and equality/order on them is
decidable — you just have to align the exponents first.

Given `n₁ · β^{e₁}` and `n₂ · β^{e₂}`, assume WLOG `e₁ ≤ e₂`. Then

```
n₂ · β^{e₂} = (n₂ · β^{e₂−e₁}) · β^{e₁}
```

so both sides now sit at exponent `e₁`, and

```
n₁ · β^{e₁}  <  n₂ · β^{e₂}     ⟺     n₁  <  n₂ · β^{e₂−e₁}
```

The right-hand side is a comparison of two `Int`s. Fully computable.

> **Why align *down* rather than up?** Aligning to the smaller exponent lets you
> multiply the other mantissa by a *positive* power of β, staying in `Int`.
> Aligning up would require division and a divisibility side condition. The
> `.natAbs` in `F2R_change_exp` exists for exactly this: `(e₂ − e₁)` is a
> nonnegative `Int` under the hypothesis, and `.natAbs` converts it to the `ℕ`
> that `β ^ _` wants.

---

## 4. Build it

### Step 1 — the dyadic primitives

```lean
def signedMantissa (s : Bool) (m : Nat) : Int :=
  if s then -(m : Int) else (m : Int)

def dyadicLt (beta : Int) (n₁ e₁ n₂ e₂ : Int) : Bool :=
  if e₁ ≤ e₂ then n₁ < n₂ * beta ^ (e₂ - e₁).natAbs
  else n₁ * beta ^ (e₁ - e₂).natAbs < n₂

def dyadicEq (beta : Int) (n₁ e₁ n₂ e₂ : Int) : Bool :=
  if e₁ ≤ e₂ then n₁ = n₂ * beta ^ (e₂ - e₁).natAbs
  else n₁ * beta ^ (e₁ - e₂).natAbs = n₂
```

No `noncomputable`. If you typo this in a way that reintroduces a real, Lean
will now tell you, because these definitions are outside the `open Classical`
scope of `PrimFloat.lean`.

Note `n₁ < n₂ * ...` in a `Bool`-typed position: Lean inserts the coercion
`decide (n₁ < n₂ * ...)` automatically, using the *genuine* `Int.decLt`
instance. That coercion is why `decide_eq_true_eq` shows up in the proofs.

### Step 2 — the correspondence theorems

```lean
variable {beta : Int} [ValidRadix beta]

private theorem val_align (n e e' : Int) (he : e' ≤ e) :
    F2R (FlocqFloat.mk n e : FlocqFloat beta)
      = F2R (FlocqFloat.mk (n * beta ^ (e - e').natAbs) e' : FlocqFloat beta) :=
  F2R_change_exp (beta := beta) (f := FlocqFloat.mk n e) (e' := e')
    ValidRadix.valid he

theorem dyadicLt_iff (n₁ e₁ n₂ e₂ : Int) :
    dyadicLt beta n₁ e₁ n₂ e₂ = true
      ↔ F2R (FlocqFloat.mk n₁ e₁ : FlocqFloat beta)
          < F2R (FlocqFloat.mk n₂ e₂ : FlocqFloat beta) := by
  unfold dyadicLt
  split
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₂ e₂ e₁ h]
      exact lt_F2R_iff (beta := beta) e₁ _ _ ValidRadix.valid
  · next h =>
      rw [decide_eq_true_eq, val_align (beta := beta) n₁ e₁ e₂ (not_le.mp h).le]
      exact lt_F2R_iff (beta := beta) e₂ _ _ ValidRadix.valid
```

Read the first branch: rewrite the *right* operand down to `e₁` (it has the
larger exponent), at which point the goal is literally `lt_F2R_iff` at exponent
`e₁`. The second branch is the mirror image.

**Three traps here, all of which cost me a build cycle:**

1. **`F2R` is ambiguous.** There is a `_root_.F2R` as well as
   `FloatSpec.Core.Defs.F2R`. `open FloatSpec.Core.Defs` makes every mention
   ambiguous. Qualify fully, or open selectively:
   `open FloatSpec.Core.Defs (FlocqFloat)`.
2. **`ValidRadix` and `FlocqFloat` live in different namespaces.** `ValidRadix`
   is declared at `Defs.lean:46`, *before* `namespace FloatSpec.Core.Defs` opens
   at line 57, so it is `_root_.ValidRadix`. `FlocqFloat` is at line 70, inside.
   Easy to get backwards.
3. **`if_pos`/`if_neg`/`if_true`/`if_false` are deprecated** and this repo treats
   deprecation as an error. Use the `split` tactic instead — it case-splits the
   `ite` and binds the hypothesis via `next h =>`, with no lemma names to rot.

`le_of_not_le` also no longer exists; write `(not_le.mp h).le`.

### Step 3 — lift to `StandardFloat`

Factor `SF2R` through a payload projection so the fallthrough arm is uniform:

```lean
def payload : StandardFloat → Int × Int
  | StandardFloat.S754_finite s m e => (signedMantissa s m, e)
  | _ => (0, 0)

theorem SF2R_eq_payload (x : StandardFloat) :
    SF2R 2 x = F2R (FlocqFloat.mk (payload x).1 (payload x).2 : FlocqFloat 2) := by
  cases x <;> simp [SF2R, payload, signedMantissa]
```

Mapping zero/infinity/NaN to `(0, 0)` is what makes this a theorem: `SF2R` sends
all three to `0`, and `F2R ⟨0, 0⟩ = 0` by the `@[simp]` lemma `F2R_zero`.

Now mirror `SFltb` **arm for arm**, changing only the last line:

```lean
def SFltbC (x y : StandardFloat) : Bool :=
  match x, y with
  | StandardFloat.S754_nan, _ => false
  | _, StandardFloat.S754_nan => false
  | StandardFloat.S754_infinity sx, StandardFloat.S754_infinity sy => sx && !sy
  | StandardFloat.S754_infinity sx, _ => sx
  | _, StandardFloat.S754_infinity sy => !sy
  | x, y => dyadicLt 2 (payload x).1 (payload x).2 (payload y).1 (payload y).2
```

> **Why mirror the arms instead of writing something cleaner?** Because the
> equivalence proof is then a mechanical `cases x <;> cases y`, and because the
> NaN/infinity arms encode IEEE 754 §5.11 semantics that are *not* derivable
> from the dyadic order: NaN is unordered with everything including itself, and
> ±∞ bracket the finite range. If you "simplify" by routing infinities through
> the dyadic path you will silently make `+∞ == 0`, since `payload` sends
> infinity to `(0,0)`. The arm order is load-bearing.

The equivalence proof:

```lean
@[simp] theorem SFltbC_eq (x y : StandardFloat) :
    SFltbC x y = FaithfulPrimFloat.SFltb x y := by
  cases x <;> cases y <;>
    simp only [SFltbC, FaithfulPrimFloat.SFltb] <;>
    rw [Bool.eq_iff_iff, dyadicLt_iff, decide_eq_true_eq,
        SF2R_eq_payload, SF2R_eq_payload]
```

16 cases. The 12 NaN/infinity ones are closed by `simp only` unfolding to
identical right-hand sides. The 4 zero/finite ones reach the `rw` chain:
`Bool.eq_iff_iff` turns `a = b` into `a = true ↔ b = true`, `dyadicLt_iff`
rewrites the left to a real comparison, `decide_eq_true_eq` strips the coercion
on the right, and the two `SF2R_eq_payload` rewrites make both sides identical.

### Step 4 — the derived layers come free

```lean
def eqbC (x y : PrimitiveFloat) : Bool := SFeqbC (Prim2SF x) (Prim2SF y)
@[simp] theorem eqbC_eq (x y : PrimitiveFloat) :
    eqbC x y = FaithfulPrimFloat.eqb x y := by
  simp only [eqbC, FaithfulPrimFloat.eqb, SFeqbC_eq]
```

`eqb`/`ltb`/`leb`/`compare` and `Beqb`/`Bltb`/`Bleb`/`Bcompare` are *pure
wrappers* composing the `SF*` functions with `Prim2SF` / `B2SF`. Both
projections were already computable (`def`, not `noncomputable`) — they just
rearrange constructors. So fixing the `SF*` layer lifts all eight for free, and
the proofs are one `simp only` each.

This is worth pausing on: the noncomputability was **one bug in one place**,
amplified eight times by ordinary composition. Finding the root rather than
patching leaves is most of the value.

Note that `compare` and the `B*` names are ambiguous with `_root_` versions;
qualify as `FaithfulPrimFloat.compare` etc.

---

## 5. Prove you actually fixed it

A build passing is not evidence. Three independent checks:

**Kernel reduction** — `decide +kernel` forces the *kernel* to evaluate the
term. This is impossible for a noncomputable definition, so each of these is a
direct refutation of the original problem:

```lean
example : SFeqbC (fin false 3 (-1)) (fin false 6 (-2)) = true := by decide +kernel
example : SFeqbC (StandardFloat.S754_zero false) (StandardFloat.S754_zero true) = true := by
  decide +kernel
example : SFeqbC StandardFloat.S754_nan StandardFloat.S754_nan = false := by decide +kernel
```

**Compiled code** — `decide +kernel` proves kernel reducibility but not that the
*compiler* emitted anything. A `#eval`'d `IO` loop over 20,000 randomized
payload pairs closes that gap, checking trichotomy, reflexivity,
`leb = lt ∨ eq`, radix-rescaling invariance (`m·2^e == 2m·2^(e−1)` — this is the
one that actually exercises the alignment path), and compare/Boolean agreement.
This is the house style; see `FloatSpec/Test/BitsExecution.lean`.

**Axiom hygiene** —
```
#print axioms SFltbC_eq
-- [propext, Classical.choice, Quot.sound]
```
The three standard Mathlib axioms, nothing custom, no `sorryAx`. `Classical.choice`
appearing here is expected and fine: the *proofs* may be classical, the
*definitions* are what must compute.

Then run the repo's own gates, which are the real acceptance criteria:
```
lake build                                  # 3102 jobs, clean
python3 scripts/check_proof_debts.py        # still exactly 4 pre-existing obligations
./scripts/audit_placeholders.sh --json FloatSpec
```

---

## 6. The general lesson

The pattern generalizes past floating point:

> When a specification is stated over a non-computable domain, do not choose
> between faithfulness and executability. Ship **both**, plus a theorem that
> they agree.

The specification (`SFeqb`, defined over ℝ, matching Flocq line for line) stays
exactly as it was — the `@[flocq_source]` correspondence is untouched. The
implementation (`SFeqbC`, defined over ℤ) is what runs. `SFeqbC_eq` is the
bridge, and being `@[simp]` means downstream proofs can move between them for
free.

This is the same architecture FloatLib describes as "every certified backend is
proved equal to a complete encoded specification," and the same architecture as
CompCert's verified compiler passes. It is the standard answer, and it is worth
recognizing the shape when you hit it.

**The cheapest prevention:** don't write blanket `open Classical` at the top of a
file that also defines `Bool`-returning functions. Prefer `open scoped Classical`
inside the specific proofs that need it, so a `decide` over reals fails loudly at
the line where it is written. A repo linter — *"a `Bool`-returning definition
whose argument types contain no `ℝ` must not be `noncomputable`"* — would have
caught all twelve of these at authoring time, and would fit the existing
`linter.coqSource` pattern in this codebase.
