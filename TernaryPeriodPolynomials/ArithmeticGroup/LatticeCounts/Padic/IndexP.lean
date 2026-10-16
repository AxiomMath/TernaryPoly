module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.Normed.MulAction
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
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.ZMod
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Peel
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# The index `[ℤ_p : pℤ_p] = p`

Formalized by Claude Haiku 5.5.

The quotient `ℤ_[p] ⧸ (p)` is the residue field `ℤ/pℤ`, so it has `p` elements.
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.PadicIndex

variable (p : ℕ) [Fact p.Prime]

/-- The additive index of the maximal ideal `(p)` in `ℤ_[p]` is `p`: it is the kernel of the
surjection `ℤ_[p] → ZMod p`, so the index is the cardinality of its image, `ZMod p`. -/
theorem index_maximalIdeal : (IsLocalRing.maximalIdeal ℤ_[p]).toAddSubgroup.index = p := by
  have hsurj : Function.Surjective (PadicInt.toZMod (p := p)) :=
    ZMod.ringHom_surjective _
  have hker : (IsLocalRing.maximalIdeal ℤ_[p]).toAddSubgroup =
      (PadicInt.toZMod (p := p)).toAddMonoidHom.ker := by
    rw [← PadicInt.ker_toZMod]
    rfl
  have hrange : (PadicInt.toZMod (p := p)).toAddMonoidHom.range = ⊤ := by
    rw [AddMonoidHom.range_eq_top]
    exact hsurj
  rw [hker, AddSubgroup.index_ker, hrange,
    Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- The additive index of `(p)` in `ℤ_[p]` is `p`. -/
theorem index_span_p : (Ideal.span {(p : ℤ_[p])}).toAddSubgroup.index = p := by
  rw [← maximalIdeal_eq_span_p]
  exact index_maximalIdeal p

end TernaryPeriodPolynomials.Argument.LatticeCounts.PadicIndex
