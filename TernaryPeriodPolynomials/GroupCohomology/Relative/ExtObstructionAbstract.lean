module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.ComposableArrows
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.Finite
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
namespace TernaryPoly.RelativeExtObstructionAbstract
open CategoryTheory CategoryTheory.Abelian

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The exact contravariant Ext segment kills the middle obstruction when both outside terms vanish. -/
theorem ext_one_subsingleton {S : ShortComplex C} (hS : S.ShortExact) (E : C)
    [Subsingleton (Ext S.X₂ E 1)] [Subsingleton (Ext S.X₃ E 2)] :
    Subsingleton (Ext S.X₁ E 1) := by
  have hz (x : Ext S.X₁ E 1) : x = 0 := by
    obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS E x (n₁ := 2) rfl (Subsingleton.elim _ _)
    have hy0 : y = 0 := Subsingleton.elim _ _
    rw [hy0,Ext.comp_zero] at hy
    exact hy.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Vanishing of the quotient's Ext¹ makes restriction on genuine morphisms surjective. -/
theorem extends_of_ext_one_subsingleton {S : ShortComplex C} (hS : S.ShortExact) (E : C)
    [Subsingleton (Ext S.X₃ E 1)] (f : S.X₁ ⟶ E) :
    ∃ F : S.X₂ ⟶ E, S.f ≫ F = f := by
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS E (Ext.mk₀ f) (n₁ := 1) rfl (Subsingleton.elim _ _)
  obtain ⟨F,rfl⟩ := (Ext.mk₀_bijective S.X₂ E).surjective y
  refine ⟨F,?_⟩
  apply (Ext.mk₀_bijective S.X₁ E).injective
  simpa only [Ext.mk₀_comp_mk₀] using hy

/-- The two short exact sequences give the extension implication with both Ext assumptions explicit. -/
theorem extends_of_two_ext_vanishings {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (hQ : S.X₃ = T.X₁) (E : C)
    [Subsingleton (Ext T.X₂ E 1)] [Subsingleton (Ext T.X₃ E 2)]
    (f : S.X₁ ⟶ E) : ∃ F : S.X₂ ⟶ E, S.f ≫ F = f := by
  have : Subsingleton (Ext T.X₁ E 1) := ext_one_subsingleton hT E
  have : Subsingleton (Ext S.X₃ E 1) := by rwa [hQ]
  exact extends_of_ext_one_subsingleton hS E f

end TernaryPoly.RelativeExtObstructionAbstract
