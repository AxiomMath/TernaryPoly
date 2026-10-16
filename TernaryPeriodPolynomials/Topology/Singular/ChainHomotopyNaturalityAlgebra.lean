module

public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Algebra.Module.End
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
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
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularChainHomotopyNaturality
open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X Y X' Y' : SimplicialObject C} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- Every component of the pinned alternating-prism chain homotopy is natural under a literal
commuting square of its combinatorial homotopy components. -/
theorem toChainHomotopy_natural (H : SimplicialObject.Homotopy f g)
    (H' : SimplicialObject.Homotopy f' g') (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : ∀ n (i : Fin (n+1)), u.app (op ⦋n⦌) ≫ H.h i = H'.h i ≫ v.app (op ⦋n+1⦌))
    (p q : ℕ) :
    ((alternatingFaceMapComplex C).map u).f p ≫ H.toChainHomotopy.hom p q =
      H'.toChainHomotopy.hom p q ≫ ((alternatingFaceMapComplex C).map v).f q := by
  change u.app (op ⦋p⦌) ≫ SimplicialObject.Homotopy.ToChainHomotopy.hom H p q =
    SimplicialObject.Homotopy.ToChainHomotopy.hom H' p q ≫ v.app (op ⦋q⦌)
  by_cases hpq : p+1 = q
  · subst q
    simp only [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,Preadditive.comp_neg,
      Preadditive.neg_comp,Preadditive.comp_sum,Preadditive.sum_comp,
      Preadditive.comp_zsmul,Preadditive.zsmul_comp,h]
  · simp only [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero _ _ _ hpq,
      comp_zero,zero_comp]

end TernaryPoly.SingularChainHomotopyNaturality
