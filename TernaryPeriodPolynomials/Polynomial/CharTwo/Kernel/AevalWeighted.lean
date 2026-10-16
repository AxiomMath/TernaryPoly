module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial

/-- **STEP2b building block.** If an algebra evaluation `aeval g` sends every generator `i : σ`
to an element `g i` of a (possibly different) polynomial ring that is itself weighted-homogeneous
of degree `w i` (matching `i`'s own weight under `w`), then `aeval g` carries a `w`-weighted-
homogeneous polynomial of degree `n` to a `w'`-weighted-homogeneous element of the SAME degree
`n`. This is the "graded algebra hom" fact needed to transport `invariantEval` (which sends the
three formal generators to `d4,d6,d7`, each already homogeneous of the matching degree 4,6,7)
across weighted-homogeneous degrees. -/
theorem isWeightedHomogeneous_aeval {R : Type*} [CommSemiring R] {σ τ : Type*}
    (w : σ → ℕ) (w' : τ → ℕ) (g : σ → MvPolynomial τ R)
    (hg : ∀ i, MvPolynomial.IsWeightedHomogeneous w' (g i) (w i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : MvPolynomial.IsWeightedHomogeneous w p n) :
    MvPolynomial.IsWeightedHomogeneous w' (MvPolynomial.aeval g p) n := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact MvPolynomial.isWeightedHomogeneous_zero R w' n
  | add p q hp hq ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hr =>
      rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
      have hprod := MvPolynomial.IsWeightedHomogeneous.prod d.support (fun i => g i ^ d i)
        (fun i => d i • w i) (fun i _ => (hg i).pow (d i))
      have hdeg : (∑ i ∈ d.support, d i • w i) = n := by
        have hw := Finsupp.weight_apply w d
        rw [hr] at hw
        exact hw.symm
      rw [hdeg] at hprod
      exact hprod.C_mul r

end TernaryPeriodPolynomials.Argument.CharTwoKernel
