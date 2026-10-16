module

public import TernaryPeriodPolynomials.Topology.Singular.ChainHomotopyNaturalitySSet
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularChainHomotopyNaturality
open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal AlgebraicTopology Simplicial

universe v u w
variable {X Y X' Y' : TopCat.{w}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The actual singular simplicial homotopy preserves a commuting square of topological prism maps. -/
theorem toSSet_prism_natural (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (h : (u ▷ TopCat.I) ≫ H.h = H'.h ≫ v) :
    (TopCat.toSSet.map u ▷ Δ[1]) ≫ H.toSSet.h = H'.toSSet.h ≫ TopCat.toSSet.map v := by
  change (TopCat.toSSet.map u ▷ Δ[1]) ≫ (TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI) ≫
      μ TopCat.toSSet X TopCat.I ≫ TopCat.toSSet.map H.h =
    ((TopCat.toSSet.obj X' ◁ SSet.stdSimplex.toSSetObjI) ≫ μ TopCat.toSSet X' TopCat.I ≫
      TopCat.toSSet.map H'.h) ≫ TopCat.toSSet.map v
  rw [← Category.assoc _ _ (μ _ _ _ ≫ _),← whisker_exchange,Category.assoc,
    μ_natural_left_assoc,← Functor.map_comp,h,Functor.map_comp]
  simp only [Category.assoc]

/-- A pointwise commuting square of genuine topological homotopies is a commuting square of their
literal prism maps, with the same interval parameter. -/
theorem top_prism_natural (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (h : ∀ t x, H (t,u x) = v (H' (t,x))) :
    (u ▷ TopCat.I) ≫ H.h = H'.h ≫ v := by
  ext x
  exact h _ _

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- The actual pinned singular chain homotopy is natural under every commuting square of genuine
topological homotopies, in all degrees and for arbitrary permitted coefficients. -/
theorem singularChainHomotopy_natural (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (h : ∀ t x, H (t,u x) = v (H' (t,x)))
    (R : C) (p q : ℕ) :
    (((singularChainComplexFunctor C).obj R).map u).f p ≫
        (H.singularChainComplexFunctorObjMap R).hom p q =
      (H'.singularChainComplexFunctorObjMap R).hom p q ≫
        (((singularChainComplexFunctor C).obj R).map v).f q :=
  sSet_chainHomotopy_natural H.toSSet H'.toSSet (TopCat.toSSet.map u) (TopCat.toSSet.map v)
    (toSSet_prism_natural H H' u v (top_prism_natural H H' u v h)) R p q

end TernaryPoly.SingularChainHomotopyNaturality
