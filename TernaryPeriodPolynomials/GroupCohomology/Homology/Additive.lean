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
# Additivity of the group homology functor

`groupHomology.functor k G n : Rep k G ⥤ ModuleCat k` preserves addition of morphisms.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

universe u

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory

variable {k G : Type u} [CommRing k] [Group G]

theorem chainsMap_id_add {A B : Rep.{u} k G} (φ ψ : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) (φ + ψ) =
      groupHomology.chainsMap (MonoidHom.id G) φ + groupHomology.chainsMap (MonoidHom.id G) ψ := by
  ext i x a
  simp [Rep.add_hom]

theorem map_id_add {A B : Rep.{u} k G} (φ ψ : A ⟶ B) (n : ℕ) :
    groupHomology.map (MonoidHom.id G) (φ + ψ) n =
      groupHomology.map (MonoidHom.id G) φ n + groupHomology.map (MonoidHom.id G) ψ n := by
  unfold groupHomology.map
  rw [chainsMap_id_add]
  exact HomologicalComplex.homologyMap_add _ _ n

theorem functor_map_add {A B : Rep.{u} k G} (φ ψ : A ⟶ B) (n : ℕ) :
    (groupHomology.functor k G n).map (φ + ψ) =
      (groupHomology.functor k G n).map φ + (groupHomology.functor k G n).map ψ :=
  map_id_add φ ψ n

theorem functor_map_nsmul {A B : Rep.{u} k G} (φ : A ⟶ B) (m n : ℕ) :
    (groupHomology.functor k G n).map (m • φ) = m • (groupHomology.functor k G n).map φ := by
  induction m with
  | zero => rw [zero_smul, zero_smul, Functor.map_zero]
  | succ m ih => rw [succ_nsmul, functor_map_add, ih, succ_nsmul]

end TernaryPeriodPolynomials.Argument.GroupHomology
