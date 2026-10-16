module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.Control.Basic
public import Mathlib.Data.List.Enum
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

/-- Naturality of literal cocone maps yields the literal induced colimit square. -/
theorem colimitMap_square {J C : Type*} [Category* J] [Category* C]
    (D E : J ⥤ C) [HasColimitsOfShape J C] (α : D ⟶ E)
    (s : Cocone D) (t : Cocone E) (f : s.pt ⟶ t.pt)
    (h : ∀ j, α.app j ≫ t.ι.app j = s.ι.app j ≫ f) :
    colim.map α ≫ colimit.desc E t = colimit.desc D s ≫ f := by
  apply colimit.hom_ext
  intro j
  rw [←Category.assoc,colimit.ι_map,Category.assoc,colimit.ι_desc,
    ←Category.assoc,colimit.ι_desc]
  exact h j

end TernaryPoly.SmoothSingularGlobal
