module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! The finite inner-product algebra behind both genuine weak scalar Leibniz rules. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-- A compact-test adjoint product rule gives the positive weak exterior commutator. -/
theorem weakScalar_add_inner (M₀ : H₀ →L[ℝ] H₀) (M₁ : H₁ →L[ℝ] H₁) (E : H₀ →L[ℝ] H₁)
    (x : H₀) (z b χb : H₁) (δb δχb : H₀)
    (hM₀ : inner ℝ (M₀ x) δb = inner ℝ x (M₀ δb))
    (hM₁ : inner ℝ (M₁ z) b = inner ℝ z (M₁ b))
    (hχ : M₁ b = χb) (hδ : δχb = M₀ δb - E.adjoint b)
    (hw : inner ℝ z χb = inner ℝ x δχb) :
    inner ℝ (M₁ z + E x) b = inner ℝ (M₀ x) δb := by
  rw [inner_add_left, hM₁, ← E.adjoint_inner_right, hχ, hw, hδ,
    inner_sub_right, sub_add_cancel, ← hM₀]

/-- A compact-test exterior product rule gives the negative weak adjoint commutator. -/
theorem weakScalar_sub_inner (M₀ : H₀ →L[ℝ] H₀) (M₁ : H₁ →L[ℝ] H₁) (E : H₀ →L[ℝ] H₁)
    (x : H₁) (z a χa : H₀) (da dχa : H₁)
    (hM₀ : inner ℝ (M₀ z) a = inner ℝ z (M₀ a))
    (hM₁ : inner ℝ (M₁ x) da = inner ℝ x (M₁ da))
    (hχ : M₀ a = χa) (hd : dχa = M₁ da + E a)
    (hw : inner ℝ z χa = inner ℝ x dχa) :
    inner ℝ (M₀ z - E.adjoint x) a = inner ℝ (M₁ x) da := by
  rw [inner_sub_left, hM₀, E.adjoint_inner_left, hχ, hw, hd,
    inner_add_right, add_sub_cancel_right, ← hM₁]

end TernaryPoly.PolynomialFormConnection
