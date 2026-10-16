module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Control.Basic
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits
variable {J C D : Type*} [Category* J] [Category* C] [Category* D]
  [HasColimitsOfShape J C] [HasColimitsOfShape J D]
  (P : J ⥤ C) (Q : J ⥤ D) (F : D ⥤ C) (i : P ⟶ Q ⋙ F)

/-- A diagram map followed by the canonical colimit comparison has its literal component maps. -/
theorem scalarColimit_ι (j : J) :
    colimit.ι P j ≫ (colim.map i ≫ colimit.post Q F) =
      i.app j ≫ F.map (colimit.ι Q j) := by
  rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_post]

/-- An actual compatible relative comparison gives the same square after taking the support colimit. -/
theorem scalarColimit_square (p : Cocone P) (q : Cocone Q) (a : p.pt ⟶ F.obj q.pt)
    (h : ∀ j, p.ι.app j ≫ a = i.app j ≫ F.map (q.ι.app j)) :
    colimit.desc P p ≫ a = (colim.map i ≫ colimit.post Q F) ≫ F.map (colimit.desc Q q) := by
  apply colimit.hom_ext
  intro j
  rw [← Category.assoc, colimit.ι_desc, ← Category.assoc, scalarColimit_ι,
    Category.assoc, ← F.map_comp, colimit.ι_desc]
  exact h j

end TernaryPoly.SmoothSingularGlobal
