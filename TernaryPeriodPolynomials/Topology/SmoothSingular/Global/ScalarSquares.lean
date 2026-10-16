module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
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
open CategoryTheory

/-- Two support maps commute whenever their literal maps into the common ambient object do. -/
theorem supportSquare_of_mono {C : Type*} [Category* C]
    {Q₀ Q₁ R₀ R₁ Q R : C} (q₀ : Q₀ ⟶ Q) (q₁ : Q₁ ⟶ Q)
    (r₀ : R₀ ⟶ R) (r₁ : R₁ ⟶ R) [Mono r₁]
    (s : Q₀ ⟶ Q₁) (t : R₀ ⟶ R₁) (i₀ : Q₀ ⟶ R₀) (i₁ : Q₁ ⟶ R₁) (a : Q ⟶ R)
    (hs : s ≫ q₁ = q₀) (ht : t ≫ r₁ = r₀)
    (h₀ : i₀ ≫ r₀ = q₀ ≫ a) (h₁ : i₁ ≫ r₁ = q₁ ≫ a) :
    s ≫ i₁ = i₀ ≫ t := by
  apply (cancel_mono r₁).mp
  rw [Category.assoc, h₁, ← Category.assoc, hs, Category.assoc, ht, h₀]

end TernaryPoly.SmoothSingularGlobal
