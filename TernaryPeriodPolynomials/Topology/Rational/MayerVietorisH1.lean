module

public import TernaryPeriodPolynomials.Topology.Rational.MayerVietorisKernel

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalMayerVietoris
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open RationalSingularAugmentation ContractibleSingularHomology
variable {X : Type} [TopologicalSpace X] (U V : Opens X) (hUV : U ⊔ V = ⊤)
variable [ContractibleSpace U] [ContractibleSpace V]

/-- Genuine MV exactness identifies H1 with the kernel of the signed overlap map. -/
def homologyOneKernelIso : (chains X).homology 1 ≅ kernel (leftMapZero U V hUV) := by
  refine (smallChains_homologyIso ℚ (TopCat.of X)
    (twoSetCover (X := TopCat.of X) U V hUV) 1).symm ≪≫ ?_
  have hz : IsZero ((mvShortComplex ℚ (X := TopCat.of X) U V hUV).X₂.homology 1) :=
    isZero_mvX₂_homology ℚ (X := TopCat.of X) U V hUV 1
      ((homology_isZero (X := U) 1 (by decide)).of_iso
        (SingularSubdivision.supportedHomologyIso X U 1))
      ((homology_isZero (X := V) 1 (by decide)).of_iso
        (SingularSubdivision.supportedHomologyIso X V 1))
  have : Mono ((mvShortExact ℚ (X := TopCat.of X) U V hUV).δ 1 0 rfl) :=
    ((mvShortExact ℚ (X := TopCat.of X) U V hUV).homology_exact₃ 1 0 rfl).mono_g
      (hz.eq_of_src _ _)
  exact ((mvShortExact ℚ (X := TopCat.of X) U V hUV).homology_exact₁ 1 0 rfl).fIsKernel.conePointUniqueUpToIso
    (limit.isLimit _)

/-- H1 of an actual two-open contractible cover is the actual reduced H0 of its overlap. -/
def homologyOneReducedIso : (chains X).homology 1 ≅
    kernel (augmentation (↥((U : Set X) ∩ (V : Set X)))) :=
  homologyOneKernelIso U V hUV ≪≫ kernel_leftMapZero_iso U V hUV ≪≫
    kernelIsIsoComp (SingularSubdivision.supportedHomologyIso X
      ((U : Set X) ∩ (V : Set X)) 0).hom _

end TernaryPoly.RationalMayerVietoris
