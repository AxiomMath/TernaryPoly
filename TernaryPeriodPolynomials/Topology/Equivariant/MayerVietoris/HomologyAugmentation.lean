module

public import TernaryPeriodPolynomials.Topology.Equivariant.MayerVietoris.HomologyFunctor
public import TernaryPeriodPolynomials.Topology.Singular.ComponentAugmentationHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantMayerVietorisHomology
open CategoryTheory Limits HomologicalComplex EquivariantSingularResolution SingularCoverNaturality

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- The homology map of the genuine coefficient-sum augmentation, for every space. -/
def homologyAugmentation : (equivariantChains G E).homology 0 ⟶ Rep.trivial ℚ G ℚ :=
  homologyMap (augmentationChain G E) 0 ≫
    (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (Rep.trivial ℚ G ℚ)).hom

/-- The augmentation of a zero-cycle class is its actual chain coefficient sum. -/
theorem zeroClass_homologyAugmentation :
    ((equivariantChains G E).cycles₀Iso.inv ≫ (equivariantChains G E).homologyπ 0) ≫
      homologyAugmentation G E=augmentation G E := by
  have h := SingularComponentAugmentation.zeroClass_augmentation (equivariantChains G E)
    (Rep.trivial ℚ G ℚ) (augmentationChain G E)
  exact (Category.assoc _ _ _).trans h

variable {G E} {F : TopCat.{0}} [MulAction G F] [ContinuousConstSMul G F]

/-- Every actual equivariant continuous map preserves the genuine augmentation on H0. -/
theorem homologyAugmentation_natural (f : E ⟶ F) (hf : ∀ (g : G) x,f (g • x)=g • f x) :
    homologyMap (chainMap f hf) 0 ≫ homologyAugmentation G F=homologyAugmentation G E := by
  have h := congrArg (fun f => homologyMap f 0) (chainMap_augmentationChain f hf)
  rw [homologyMap_comp] at h
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun m => m ≫ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (Rep.trivial ℚ G ℚ)).hom) h)

end TernaryPoly.EquivariantMayerVietorisHomology
