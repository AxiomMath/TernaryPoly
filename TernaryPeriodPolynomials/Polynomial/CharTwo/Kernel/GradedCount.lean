module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.SetTheory.Cardinal.Finite
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





noncomputable section

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

/-- **STEP2 building block.** For a finite-variable polynomial ring over `ZMod 2` graded by a
weight function `w` with no zero weights, the `R`-rank of the weighted-homogeneous-degree-`n`
submodule equals the number of exponent vectors of that weighted degree. This is the Mathlib
translation of "the Hilbert series coefficient counts monomials of a given weighted degree",
needed to connect the `geom`/`P` generating-function identity of `HilbertSeries.lean` to actual
`finrank` facts about `TernaryPoly.DicksonQuotient.Poly` and its invariant subring. -/
theorem finrank_weightedHomogeneousSubmodule {σ : Type*} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) :
    Module.finrank (ZMod 2) (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) w n) =
      Nat.card {d : σ →₀ ℕ | Finsupp.weight w d = n} := by
  have : Nontrivial (ZMod 2) := ⟨⟨0, 1, by decide⟩⟩
  have hfin : {d : σ →₀ ℕ | Finsupp.weight w d = n}.Finite :=
    Finsupp.finite_of_nat_weight_eq w hw n
  let _ : Fintype {d : σ →₀ ℕ | Finsupp.weight w d = n} := hfin.fintype
  rw [Nat.card_eq_fintype_card, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_card_basis
    (Finsupp.basisSingleOne.map
      (AddMonoidAlgebra.supportedEquivFinsupp (R := ZMod 2) (S := ZMod 2)
        {d : σ →₀ ℕ | Finsupp.weight w d = n}).symm)

end TernaryPeriodPolynomials.Argument.CharTwoKernel
