module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C]

/-- Exactness transports through actual isomorphisms and specified commuting squares. -/
theorem exact_transport (S : ShortComplex C) (hS : S.Exact) {A B D : C}
    (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (a : A ⟶ B) (b : B ⟶ D) (hab : a ≫ b = 0)
    (h₁ : S.f ≫ e₂.hom = e₁.hom ≫ a) (h₂ : S.g ≫ e₃.hom = e₂.hom ≫ b) :
    (ShortComplex.mk a b hab).Exact :=
  ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁.symm h₂.symm) hS

/-- An exact pair of actual rational linear maps glues precisely its compatible elements. -/
theorem exact_lift_iff {A B D : ModuleCat.{0} ℚ} (a : A ⟶ B) (b : B ⟶ D)
    (hab : a ≫ b = 0) (he : (ShortComplex.mk a b hab).Exact) (y : B) :
    b y = 0 ↔ ∃ x, a x = y := by
  change y ∈ LinearMap.ker b.hom ↔ y ∈ LinearMap.range a.hom
  rw [he.moduleCat_range_eq_ker]

/-- If the preceding object vanishes, exactness forces the outgoing map to be injective. -/
theorem injective_of_exact_of_isZero {A B D : ModuleCat.{0} ℚ} (a : A ⟶ B) (b : B ⟶ D)
    (hab : a ≫ b = 0) (he : (ShortComplex.mk a b hab).Exact) (hA : IsZero A) :
    Function.Injective b := by
  have ha : a = 0 := hA.eq_of_src _ _
  have hb : Mono b := (ShortComplex.exact_iff_mono (S := ShortComplex.mk a b hab) ha).mp he
  exact (ModuleCat.mono_iff_injective b).mp hb

end TernaryPoly.RationalRelativeSupport
