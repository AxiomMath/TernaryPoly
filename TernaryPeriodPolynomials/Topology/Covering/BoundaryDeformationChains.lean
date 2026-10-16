module

public import TernaryPeriodPolynomials.Topology.Singular.ChainHomotopyNaturalityTop
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains

@[expose] public section

noncomputable section
namespace TernaryPoly.CoveringBoundaryDeformation.Chains
open CategoryTheory AlgebraicTopology
open EquivariantSingularResolution SingularCoverNaturality FreeActionLinearization
open scoped unitInterval
variable {G : Type} [Group G] {E F : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G F] [ContinuousConstSMul G F]
  {f g : E ⟶ F} (H : TopCat.Homotopy f g)
  (hH : ∀ (a : G) (t : I) (x : E), H (t, a • x) = a • H (t, x))

include hH in
/-- Naturality of the actual singular prism gives equivariance in every degree. -/
theorem prism_equivariant (a : G) (i j : ℕ) :
    (scalarChainMap G E a).f i ≫ (H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).hom i j =
      (H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).hom i j ≫
        (scalarChainMap G F a).f j :=
  SingularChainHomotopyNaturality.singularChainHomotopy_natural H H
    (scalarMap G E a) (scalarMap G F a) (fun t x => hH a t x) (ModuleCat.of ℚ ℚ) i j

/-- The literal singular prism, as an intertwiner of the actual chain representations. -/
def prism (i j : ℕ) : chainRep G E i ⟶ chainRep G F j :=
  Rep.ofHom ⟨((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).hom i j).hom,
    fun a => congrArg ModuleCat.Hom.hom (prism_equivariant H hH a i j)⟩

/-- A genuinely equivariant topological homotopy induces a chain homotopy in Rep ℚ G. -/
def chainHomotopy
    (hf : ∀ (a : G) (x : E), f (a • x) = a • f x)
    (hg : ∀ (a : G) (x : E), g (a • x) = a • g x) :
    _root_.Homotopy (chainMap f hf) (chainMap g hg) where
  hom := prism H hH
  zero i j hij := by
    ext x
    exact congrArg (fun m => m.hom x)
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).zero i j hij)
  comm i := by
    ext x
    exact congrArg (fun m => m.hom x)
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).comm i)

/-- Forgetting equivariance recovers the exact pinned singular homotopy component. -/
theorem chainHomotopy_component
    (hf : ∀ (a : G) (x : E), f (a • x) = a • f x)
    (hg : ∀ (a : G) (x : E), g (a • x) = a • g x) (i j : ℕ) :
    (forget₂ (Rep ℚ G) (ModuleCat ℚ)).map ((chainHomotopy H hH hf hg).hom i j) =
      (H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).hom i j := rfl

end TernaryPoly.CoveringBoundaryDeformation.Chains
