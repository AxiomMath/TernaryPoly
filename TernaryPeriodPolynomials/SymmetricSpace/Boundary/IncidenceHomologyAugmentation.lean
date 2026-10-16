module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyPositive
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyGraph
public import TernaryPeriodPolynomials.Topology.Equivariant.MayerVietoris.HomologyAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits HomologicalComplex FreeActionLinearization
open IntegralGL3Congruence SingularBoundaryRestriction SymmetricSpaceBoundaryMV
open EquivariantSingularResolution EquivariantSingularSmall EquivariantSingularMayerVietoris
open EquivariantMayerVietorisHomology SymmetricSpaceBoundaryFaceAugmentation SingularCoverNaturality
open scoped MonoidAlgebra

section Components
variable {ι : Type} (E : ι → Type) [∀ i,TopologicalSpace (E i)] [∀ i,ContractibleSpace (E i)]
  [TopologicalSpace ι] [DiscreteTopology ι]

/-- Forgetting the component label retains the literal singular coefficient augmentation. -/
theorem scalarComponent_sum : SingularComponentAugmentation.scalarAugmentation E ≫
    ModuleCat.ofHom (labelSumLinear ι)=augmentationModule (TopCat.of (SingularComponentAugmentation.Total E)) := by
  apply (TopCat.toSSet.obj (TopCat.of (SingularComponentAugmentation.Total E))).chainComplex_hom_ext
  intro simplex
  have hs : ModuleCat.ofHom (MonoidAlgebra.lsingle (TopCat.toSSetObj₀Equiv simplex).1) ≫
      ModuleCat.ofHom (labelSumLinear ι)=𝟙 (ModuleCat.of ℚ ℚ) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact labelSumLinear_single ι _ r
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ ModuleCat.ofHom (labelSumLinear ι))
      (SingularComponentAugmentation.generator_scalarAugmentation E simplex)).trans
        (hs.trans (generator_augmentation _ simplex).symm))

variable [MulAction principalSix ι] [MulAction principalSix (SingularComponentAugmentation.Total E)]
  [ContinuousConstSMul principalSix (SingularComponentAugmentation.Total E)]
  (hlabel : ∀ (g : principalSix) (x : SingularComponentAugmentation.Total E),(g • x).1=g • x.1)

theorem componentAugmentation_sum : SingularComponentAugmentation.augmentation E principalSix hlabel ≫
    labelSum=augmentation principalSix (TopCat.of (SingularComponentAugmentation.Total E)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact congrArg ModuleCat.Hom.hom (scalarComponent_sum E)

/-- The H0 component isomorphism preserves genuine coefficient augmentation. -/
theorem componentH0_sum : (SingularComponentAugmentation.homologyZeroIso E principalSix hlabel).hom ≫
    labelSum=homologyAugmentation principalSix (TopCat.of (SingularComponentAugmentation.Total E)) := by
  have : Epi (SingularComponentAugmentation.zeroClassMap E principalSix) := by
    unfold SingularComponentAugmentation.zeroClassMap
    infer_instance
  apply (cancel_epi (SingularComponentAugmentation.zeroClassMap E principalSix)).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ labelSum)
      (SingularComponentAugmentation.zeroClassMap_homologyZeroIso E principalSix hlabel)).trans
        ((componentAugmentation_sum E hlabel).trans (zeroClass_homologyAugmentation _ _).symm))

end Components

attribute [local instance] lineLabelTopology planeLabelTopology flagLabelTopology
  lineLabelDiscrete planeLabelDiscrete flagLabelDiscrete

theorem lineH0_sum : lineH0Iso.hom ≫ labelSum=homologyAugmentation principalSix (TopCat.of LineFaceSum) :=
  componentH0_sum lineFamily lineLabel_equivariant

theorem planeH0_sum : planeH0Iso.hom ≫ labelSum=homologyAugmentation principalSix (TopCat.of PlaneFaceSum) :=
  componentH0_sum planeFamily planeLabel_equivariant

theorem flagH0_sum : flagH0Iso.hom ≫ labelSum=homologyAugmentation principalSix (TopCat.of CornerFaceSum) :=
  componentH0_sum flagFamily flagLabel_equivariant

/-- The explicit H0 isomorphism furnished by actual MV and graph connectedness. -/
def boundaryH0Iso : boundaryChains.homology 0 ≅ Rep.trivial ℚ principalSix ℚ :=
  boundaryH0CokernelIso ≪≫ incidenceCokernelIso

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
