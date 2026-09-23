import FloatSpec.src.Pff.Pff

/-! Typed clients for representative `Pff.lean` statements whose shape was
reviewed against Rocq after the Hoare cutover.  Each ascription is the Lean
reading of the matching `Check` in `PffStatementContracts.v`: the same premises
in the same order and the same conclusion.  The indexed carrier
`FlocqFloat beta` with `[ValidRadix beta]` stands for Coq's `float` with
`1 < radix`; `beta = radix` (or `beta = 2` and `radix = 2` in the radix-2
discriminant sections) links that index to Coq's radix.
`scripts/test_pff_statement_contracts.py` mutates these ascriptions and both
checkers must reject each mutation. -/

namespace PffStatementContracts

open FloatSpec.Core.Defs

#check (@FnormalUnique : ∀ {beta : Int} [ValidRadix beta] (radix : Int),
  beta = radix → 1 < radix →
  ∀ (b : Fbound_skel) (precision : Nat), precision ≠ 0 →
    b.vNum = Zpower_nat radix precision →
    ∀ p q : FlocqFloat beta, Fnormal radix b p → Fnormal radix b q →
      _root_.F2R p = _root_.F2R q → p = q)

#check (@ImplyClosest : ∀ {beta : Int} [ValidRadix beta] (b : Fbound_skel)
  (radix : Int) [ValidRadix radix] (precision : Nat),
  beta = radix → 1 < radix → b.vNum = Zpower_nat radix precision → 1 < precision →
  ∀ (z : ℝ) (f : FlocqFloat beta) (e : Int), Fbounded b f → Fcanonic radix b f →
    (radix : ℝ) ^ (e + (precision : Int) - 1) ≤ z →
    (radix : ℝ) ^ (e + (precision : Int) - 1) ≤ _root_.F2R f →
    -b.dExp ≤ e → |z - _root_.F2R f| ≤ (radix : ℝ) ^ e / 2 →
    Closest b (radix : ℝ) z f)

#check (@errorBoundedMult : ∀ {beta : Int} [ValidRadix beta] (bo : Fbound_skel)
  (radix : Int) [ValidRadix radix] (precision : Nat),
  beta = radix → 1 < radix → 1 < precision → bo.vNum = Zpower_nat radix precision →
  ∀ P : ℝ → FlocqFloat beta → Prop, RoundedModeP bo P →
  ∀ p q f : FlocqFloat beta, Fbounded bo p → Fbounded bo q →
    -bo.dExp ≤ p.Fexp + q.Fexp → P (_root_.F2R p * _root_.F2R q) f →
    ∃ r : FlocqFloat beta,
      _root_.F2R r = _root_.F2R p * _root_.F2R q - _root_.F2R f ∧
        Fbounded bo r ∧ r.Fexp = p.Fexp + q.Fexp)

#check (@discri3 : ∀ {beta : Int} [ValidRadix beta] (bo : Fbound_skel) (radix : Int)
  (precision : Nat),
  beta = 2 → radix = 2 → 1 < precision → bo.vNum = Zpower_nat radix precision →
  ∀ a b b' c p q t dp dq s d : FlocqFloat beta,
    Fbounded bo p → Fbounded bo q → 0 ≤ _root_.F2R b * _root_.F2R b' →
    EvenClosest bo (radix : ℝ) precision (_root_.F2R b * _root_.F2R b') p →
    3 * |_root_.F2R p - _root_.F2R q| < _root_.F2R p + _root_.F2R q →
    EvenClosest bo (radix : ℝ) precision (_root_.F2R p - _root_.F2R q) t →
    _root_.F2R dp = _root_.F2R b * _root_.F2R b' - _root_.F2R p →
    _root_.F2R dq = _root_.F2R a * _root_.F2R c - _root_.F2R q →
    EvenClosest bo (radix : ℝ) precision (_root_.F2R dp - _root_.F2R dq) s →
    EvenClosest bo (radix : ℝ) precision (_root_.F2R t + _root_.F2R s) d →
    (∃ f : FlocqFloat beta, Fbounded bo f ∧ _root_.F2R f = _root_.F2R dp - _root_.F2R dq) →
    |_root_.F2R d - (_root_.F2R b * _root_.F2R b' - _root_.F2R a * _root_.F2R c)| ≤
      2 * Fulp bo radix precision d)

#check (@eqExpLess : ∀ {beta : Int} [ValidRadix beta] (b : Fbound_skel)
  (p q : FlocqFloat beta),
  Fbounded b p → _root_.F2R p = _root_.F2R q →
    ∃ r : FlocqFloat beta, Fbounded b r ∧ _root_.F2R r = _root_.F2R q ∧ q.Fexp ≤ r.Fexp)

end PffStatementContracts
