module

public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains
public import TernaryPeriodPolynomials.Topology.ContractibleSingularHomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantMayerVietorisHomology
open CategoryTheory Limits HomologicalComplex EquivariantSingularResolution SingularCoverNaturality

variable {G : Type} [Group G]

/-- The faithful exact forgetful functor detects equality of induced homology maps. -/
theorem homologyMap_eq_of_forget {K L : ChainComplex (Rep ℚ G) ℕ} (f g : K ⟶ L) (n : ℕ)
    (h : homologyMap (((forget₂ (Rep ℚ G) (ModuleCat ℚ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map f) n = homologyMap (((forget₂ (Rep ℚ G) (ModuleCat ℚ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map g) n) : homologyMap f n=homologyMap g n := by
  apply (forget₂ (Rep ℚ G) (ModuleCat ℚ)).map_injective
  apply (cancel_epi ((K.sc n).mapHomologyIso (forget₂ (Rep ℚ G) (ModuleCat ℚ))).hom).mp
  exact (ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor (Rep ℚ G) (ComplexShape.down ℕ) n).map f)
        (forget₂ (Rep ℚ G) (ModuleCat ℚ))).symm.trans
    ((congrArg (fun m => m ≫ ((L.sc n).mapHomologyIso
      (forget₂ (Rep ℚ G) (ModuleCat ℚ))).hom) h).trans
        (ShortComplex.mapHomologyIso_hom_naturality
          ((shortComplexFunctor (Rep ℚ G) (ComplexShape.down ℕ) n).map g)
            (forget₂ (Rep ℚ G) (ModuleCat ℚ))))

variable {E F : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G F] [ContinuousConstSMul G F]

/-- The actual equivariant map forgets to the literal singular map. -/
theorem forget_chainMap (f : E ⟶ F) (hf : ∀ (g : G) x,f (g • x)=g • f x) :
    ((forget₂ (Rep ℚ G) (ModuleCat ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (chainMap f hf) ≫ (forgetChainIso G F).hom =
      (forgetChainIso G E).hom ≫ underlyingMap f := by
  apply HomologicalComplex.hom_ext
  intro n
  ext x
  rfl

/-- Ordinary homotopy of equivariant maps gives equality on actual representation-valued homology.
No equivariance of a chosen contraction is assumed. -/
theorem homologyMap_homotopic (f g : E ⟶ F)
    (hf : ∀ (a : G) x,f (a • x)=a • f x) (hg : ∀ (a : G) x,g (a • x)=a • g x)
    (H : TopCat.Homotopy f g) (n : ℕ) : homologyMap (chainMap f hf) n=homologyMap (chainMap g hg) n := by
  apply homologyMap_eq_of_forget
  rw [←cancel_mono (homologyMap (forgetChainIso G F).hom n)]
  rw [←homologyMap_comp,←homologyMap_comp,forget_chainMap,forget_chainMap,
    homologyMap_comp,homologyMap_comp]
  exact congrArg (fun m => homologyMap (forgetChainIso G E).hom n ≫ m)
    ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq n)

/-- The singular representation map preserves identity. -/
theorem chainMap_id : chainMap (𝟙 E) (fun (_ : G) _ => rfl)=𝟙 (equivariantChains G E) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact congrArg (fun m => (m.f n).hom)
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map_id E)

variable {D : TopCat.{0}} [MulAction G D] [ContinuousConstSMul G D]

/-- Actual equivariant singular maps preserve composition. -/
theorem chainMap_comp (f : E ⟶ F) (hf : ∀ (g : G) x,f (g • x)=g • f x)
    (g : F ⟶ D) (hg : ∀ (a : G) x,g (a • x)=a • g x) :
    chainMap (f ≫ g) (fun a x => by change g (f (a • x))=a • g (f x); rw [hf,hg])=
      chainMap f hf ≫ chainMap g hg := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact congrArg (fun m => (m.f n).hom)
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map_comp f g)

/-- A genuine equivariant homotopy equivalence induces the actual homology isomorphism. -/
def spaceHomologyIso (e : ContinuousMap.HomotopyEquiv E F)
    (he : ∀ (g : G) x,e (g • x)=g • e x)
    (hi : ∀ (g : G) x,e.invFun (g • x)=g • e.invFun x) (n : ℕ) :
    (equivariantChains G E).homology n ≅ (equivariantChains G F).homology n where
  hom := homologyMap (chainMap (TopCat.ofHom e.toFun) he) n
  inv := homologyMap (chainMap (TopCat.ofHom e.invFun) hi) n
  hom_inv_id := by
    rw [←homologyMap_comp,←chainMap_comp]
    have H : TopCat.Homotopy (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 E) := e.left_inv.some
    exact (homologyMap_homotopic _ _ _ (fun (_ : G) _ => rfl) H n).trans
      ((congrArg (fun f => homologyMap f n) chainMap_id).trans (homologyMap_id _ _))
  inv_hom_id := by
    rw [←homologyMap_comp,←chainMap_comp]
    have H : TopCat.Homotopy (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 F) := e.right_inv.some
    exact (homologyMap_homotopic _ _ _ (fun (_ : G) _ => rfl) H n).trans
      ((congrArg (fun f => homologyMap f n) chainMap_id).trans (homologyMap_id _ _))

end TernaryPoly.EquivariantMayerVietorisHomology
