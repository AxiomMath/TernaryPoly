module

public import Mathlib.CategoryTheory.Iso
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

@[expose] public section


namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory

/-- Actual compact and ordinary comparisons assemble through a faithful final subdivision map. -/
theorem compactComparison_square {C : Type*} [Category* C] {A B R X Y S : C}
    (c : A ≅ B) (e : R ≅ B) (o : X ≅ Y)
    (f : A ⟶ X) (j : B ⟶ S) (r : Y ⟶ S) [Mono r] (k : R ⟶ Y) (s : X ⟶ S)
    (hE : e.hom ≫ j = k ≫ r) (hC : c.hom ≫ j = f ≫ s) (hO : o.hom ≫ r = s) :
    (c ≪≫ e.symm).hom ≫ k = f ≫ o.hom := by
  apply (cancel_mono r).mp
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [←hE,Iso.inv_hom_id_assoc,hC,hO]

/-- Two actual commuting squares compose on the nose. -/
theorem composeCommutingSquares {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ E) (d : E ⟶ D)
    (e : D ⟶ F) (f : E ⟶ G) (g : G ⟶ F)
    (h1 : a ≫ b = c ≫ d) (h2 : d ≫ e = f ≫ g) : a ≫ (b ≫ e) = (c ≫ f) ≫ g := by
  rw [←Category.assoc,h1,Category.assoc,h2,←Category.assoc]

end TernaryPoly.SmoothSingularGlobal
