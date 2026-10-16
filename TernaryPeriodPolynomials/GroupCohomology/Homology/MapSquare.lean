module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Commuting squares for the functoriality of group homology

A square of group homomorphisms `f₂ ∘ u = v ∘ f₁` together with coefficient morphisms whose composites agree as
linear maps gives a commuting square of the maps induced on group homology.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

universe u

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory Rep

variable {k : Type u} [CommRing k] {G₁ G₂ H₁ H₂ : Type u} [Group G₁] [Group G₂] [Group H₁] [Group H₂]

theorem map_square (f₁ : G₁ →* G₂) (f₂ : H₁ →* H₂) (u : G₁ →* H₁) (v : G₂ →* H₂)
    (huv : f₂.comp u = v.comp f₁) {A₁ : Rep k G₁} {A₂ : Rep k G₂} {B₁ : Rep k H₁} {B₂ : Rep k H₂}
    (φ₁ : A₁ ⟶ Rep.res u B₁) (φ₂ : B₁ ⟶ Rep.res f₂ B₂) (ψ₁ : A₁ ⟶ Rep.res f₁ A₂)
    (ψ₂ : A₂ ⟶ Rep.res v B₂)
    (hcoef : (φ₁ ≫ (Rep.resFunctor u).map φ₂).hom.toLinearMap =
      (ψ₁ ≫ (Rep.resFunctor f₁).map ψ₂).hom.toLinearMap) (n : ℕ) :
    groupHomology.map u φ₁ n ≫ groupHomology.map f₂ φ₂ n =
      groupHomology.map f₁ ψ₁ n ≫ groupHomology.map v ψ₂ n := by
  rw [← groupHomology.map_comp, ← groupHomology.map_comp]
  exact groupHomology.map_congr huv hcoef n

end TernaryPeriodPolynomials.Argument.GroupHomology
