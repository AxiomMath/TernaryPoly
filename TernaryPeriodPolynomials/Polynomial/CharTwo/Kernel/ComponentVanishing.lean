module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
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

/-- **Lemma A building block.** If every weighted-homogeneous component of `p` vanishes, `p`
itself is `0`. Proved by checking `coeff d p = 0` for every exponent `d`, specializing the
hypothesis at `n := Finsupp.weight w d` (the one degree where `coeff_weightedHomogeneousComponent`
reduces to exactly `coeff d p`). -/
theorem eq_zero_of_forall_weightedHomogeneousComponent_eq_zero {R : Type*} [CommSemiring R]
    {σ : Type*} {w : σ → ℕ} {p : MvPolynomial σ R}
    (h : ∀ n : ℕ, weightedHomogeneousComponent w n p = 0) : p = 0 := by
  ext d
  have hd := congrArg (fun q => q.coeff d) (h (Finsupp.weight w d))
  rwa [coeff_weightedHomogeneousComponent, ite_eq_left rfl, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hd

end TernaryPeriodPolynomials.Argument.CharTwoKernel
