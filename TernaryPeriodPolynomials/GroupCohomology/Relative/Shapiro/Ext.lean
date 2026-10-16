module

public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.ComposableArrows
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
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
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeShapiroExt
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Vanishing of resolved cohomology implies vanishing of derived-category Ext.
This explicitly bridges the two Ext APIs using representatives and coboundaries. -/
theorem ext_subsingleton_of_resolution_homology
    (R : Type v) [CommRing R] [Linear R C] {X E : C}
    (P : ProjectiveResolution X) (n : ℕ)
    (h : IsZero ((P.complex.linearYonedaObj R E).homology (n + 1))) :
    Subsingleton (Ext X E (n + 1)) := by
  have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr h
  rw [HomologicalComplex.exactAt_iff', ShortComplex.moduleCat_exact_iff] at hex
  · have hz (a : Ext X E (n + 1)) : a = 0 := by
      obtain ⟨f, hf, rfl⟩ := P.extMk_surjective a (n + 2) rfl
      apply (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr
      exact hex f hf
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  · simp
  · simp

/-- Actual group cohomology vanishing kills derived-category Ext from the trivial representation. -/
theorem trivial_ext_subsingleton {G : Type} [Group G] (E : Rep.{0} ℚ G) (n : ℕ)
    [HasExt.{1} (Rep.{0} ℚ G)]
    (h : IsZero (groupCohomology E (n + 1))) :
    Subsingleton (Ext.{1} (Rep.trivial ℚ G ℚ) E (n + 1)) := by
  apply ext_subsingleton_of_resolution_homology ℚ (Rep.barResolution ℚ G) n
  exact h.of_iso (groupCohomologyIso E (n + 1) (Rep.barResolution ℚ G)).symm

end TernaryPoly.RelativeShapiroExt
