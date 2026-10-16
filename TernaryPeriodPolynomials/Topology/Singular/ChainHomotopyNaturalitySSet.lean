module

public import TernaryPeriodPolynomials.Topology.Singular.ChainHomotopyNaturalityAlgebra
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Order.Fin.InsertNth
public import Mathlib.Order.Fin.Prod
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularChainHomotopyNaturality
open CategoryTheory Limits MonoidalCategory SimplicialObject Simplicial Opposite

universe v u w
variable {X Y X' Y' : SSet.{w}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The pinned prism simplex associated to a simplicial-set homotopy is natural under a literal
commuting square of the homotopy prism maps. -/
theorem sSet_combinatorial_natural (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (h : (u ▷ Δ[1]) ≫ H.h = H'.h ≫ v)
    (n : ℕ) (i : Fin (n+1)) :
    u.app (op ⦋n⦌) ≫ H.toSimplicialObjectHomotopy.h i =
      H'.toSimplicialObjectHomotopy.h i ≫ v.app (op ⦋n+1⦌) := by
  ext x
  change ((SSet.yonedaEquiv.symm (u.app _ x) ▷ Δ[1]) ≫ H.h).app _
      (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1 =
    v.app _ (((SSet.yonedaEquiv.symm x ▷ Δ[1]) ≫ H'.h).app _
      (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1)
  rw [← SSet.yonedaEquiv_symm_comp,comp_whiskerRight,Category.assoc,h,← Category.assoc]
  rfl

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- The actual pinned chain homotopy of simplicial sets is natural in every pair of degrees,
with arbitrary coefficients in a preadditive category admitting the required coproducts. -/
theorem sSet_chainHomotopy_natural (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (h : (u ▷ Δ[1]) ≫ H.h = H'.h ≫ v)
    (R : C) (p q : ℕ) :
    (SSet.chainComplexMap u R).f p ≫ (H.chainComplexMap R).hom p q =
      (H'.chainComplexMap R).hom p q ≫ (SSet.chainComplexMap v R).f q := by
  apply toChainHomotopy_natural
    (H.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj R))
    (H'.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj R))
  intro n i
  change (sigmaConst.obj R).map (u.app (op ⦋n⦌)) ≫
      (sigmaConst.obj R).map (H.toSimplicialObjectHomotopy.h i) =
    (sigmaConst.obj R).map (H'.toSimplicialObjectHomotopy.h i) ≫
      (sigmaConst.obj R).map (v.app (op ⦋n+1⦌))
  rw [← Functor.map_comp,← Functor.map_comp,sSet_combinatorial_natural H H' u v h]

end TernaryPoly.SingularChainHomotopyNaturality
