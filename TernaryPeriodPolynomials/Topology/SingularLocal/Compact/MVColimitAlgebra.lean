module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Limits.Constructions.WeaklyInitial
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Subobject.Comma
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
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits

/-- Exactness of module-valued diagrams is detected on every actual object of the index. -/
theorem diagram_exact_of_objectwise {J : Type} [SmallCategory J]
    (S : ShortComplex (J ⥤ ModuleCat.{0} ℚ))
    (hS : ∀ j, (S.map ((evaluation J (ModuleCat ℚ)).obj j)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext j
  have hj : IsZero (S.homology.obj j) :=
    IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (hS j)) (S.mapHomologyIso ((evaluation J (ModuleCat ℚ)).obj j)).symm
  exact hj.eq_of_src _ _

/-- A filtered colimit of actual exact module-valued diagrams remains exact. -/
theorem filteredColimit_exact {J : Type} [SmallCategory J] [IsFiltered J]
    (S : ShortComplex (J ⥤ ModuleCat.{0} ℚ))
    (hS : ∀ j, (S.map ((evaluation J (ModuleCat ℚ)).obj j)).Exact) :
    (S.map (colim : (J ⥤ ModuleCat ℚ) ⥤ ModuleCat ℚ)).Exact :=
  (diagram_exact_of_objectwise S hS).map _

end TernaryPoly.SingularLocalCompactMV
