module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Comparison
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory Limits AlgebraicTopology
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- The actual constant local homology is identified through the proved canonical chain isomorphism. -/
def ordinaryHomologyIso (n : ℕ) : (chains X V).homology n ≅ (ordinaryChains X V).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
    (ordinaryChainIso X V)

/-- The actual H0 augmentation is the ordinary singular augmentation composed with the
canonical chain-induced homology comparison. -/
def augmentation : (chains X V).homology 0 ⟶ V :=
  (ordinaryHomologyIso X V 0).hom ≫ X.singularHomology₀ε V

/-- On every path-connected space, the literal H0 augmentation is an isomorphism to V. -/
instance augmentation_isIso [PathConnectedSpace X] : IsIso (augmentation X V) := by
  exact ((ordinaryHomologyIso X V 0) ≪≫
    @asIso (ModuleCat.{0} ℚ) _ _ _ (X.singularHomology₀ε V)
      (TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier X V)).isIso_hom

/-- The resulting isomorphism uses the actual augmentation as its forward map. -/
def augmentationIso [PathConnectedSpace X] : (chains X V).homology 0 ≅ V :=
  asIso (augmentation X V)

/-- A genuine topological homotopy equivalence induces a chain homotopy equivalence
for arbitrary rational coefficients, with no finite-dimensional hypothesis. -/
def ordinaryChainHomotopyEquiv {Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv (ordinaryChains X V) (ordinaryChains Y V) where
  hom := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj V).map (TopCat.ofHom e.toFun)
  inv := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj V).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    rw [←Functor.map_comp]
    have H : TopCat.Homotopy ((TopCat.ofHom e.toFun) ≫ (TopCat.ofHom e.invFun)) (𝟙 X) := e.left_inv.some
    exact (H.singularChainComplexFunctorObjMap V).trans
      (_root_.Homotopy.ofEq (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj V).map_id _))
  homotopyInvHomId := by
    rw [←Functor.map_comp]
    have H : TopCat.Homotopy ((TopCat.ofHom e.invFun) ≫ (TopCat.ofHom e.toFun)) (𝟙 Y) := e.right_inv.some
    exact (H.singularChainComplexFunctorObjMap V).trans
      (_root_.Homotopy.ofEq (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj V).map_id _))

/-- Higher actual constant local homology vanishes on a contractible space for every
rational module, including infinite-dimensional modules. -/
theorem homology_isZero [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero ((chains X V).homology n) := by
  let e := ordinaryChainHomotopyEquiv X V (Y := TopCat.of Unit) (ContractibleSpace.hequiv_unit X).some
  have hU : IsZero ((ordinaryChains (TopCat.of Unit) V).homology n) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat ℚ) n V (TopCat.of Unit) hn
  exact (hU.of_iso (e.toHomologyIso n)).of_iso (ordinaryHomologyIso X V n)

end TernaryPoly.SingularLocalConstant
