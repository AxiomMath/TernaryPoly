module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportSmallTransport

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology TopologicalSpace
open SphereOddDegree

variable {X : Type} [TopologicalSpace X] (U V : Opens X) (hUV : U ⊔ V = ⊤)

/-- The actual small-sum quotient maps to the established two-open small-chain complex. -/
def smallSumToCover : supportedSmallSum (U : Set X) (V : Set X) ⟶
    twoOpenCoverSmallChains ℚ (X := TopCat.of X) U V hUV :=
  cokernel.desc (supportedDiagonal (U : Set X) (V : Set X))
    (mvRightChainMap ℚ (X := TopCat.of X) U V hUV) (mvLeft_comp_mvRight ℚ (X := TopCat.of X) U V hUV)

/-- The established signed scalar Mayer–Vietoris sequence identifies the two actual small-chain models. -/
instance smallSumToCover_isIso : IsIso (smallSumToCover U V hUV) := by
  have he := mvShortComplex_shortExact ℚ (X := TopCat.of X) U V hUV
  have : Mono (smallSumToCover U V hUV) := he.exact.mono_cokernelDesc
  have : Epi (mvRightChainMap ℚ (X := TopCat.of X) U V hUV) := he.epi_g
  have : Epi (smallSumToCover U V hUV) := epi_of_epi_fac (cokernel.π_desc _ _ _)
  exact isIso_of_mono_of_epi _

/-- The comparison of small models preserves the literal inclusion into full chains. -/
theorem smallSumToCover_inclusion :
    smallSumToCover U V hUV ≫ smallChainsInclusion ℚ (TopCat.of X) (twoSetCover U V hUV) =
      supportedSmallSumInclusion (U : Set X) (V : Set X) := by
  apply (cancel_epi (cokernel.π (supportedDiagonal (U : Set X) (V : Set X)))).mp
  erw [← Category.assoc, smallSumToCover, cokernel.π_desc, supportedSmallSumInclusion, cokernel.π_desc]
  apply biprod.hom_ext'
  · simp only [mvRightChainMap, supportedSum, biprod.inl_desc]
    erw [biprod.inl_desc_assoc]
    ext n c
    rfl
  · simp only [mvRightChainMap, supportedSum, biprod.inr_desc]
    erw [biprod.inr_desc_assoc]
    ext n c
    rfl

include hUV in
/-- Actual small-sum inclusion is a quasi-isomorphism for a two-open cover, by subdivision. -/
theorem supportedSmallSumInclusion_quasiIso :
    QuasiIso (supportedSmallSumInclusion (U : Set X) (V : Set X)) := by
  rw [← smallSumToCover_inclusion U V hUV]
  exact quasiIso_comp (hφ := inferInstance)
    (hφ' := smallChains_inclusion_quasiIso ℚ (TopCat.of X) (twoSetCover U V hUV))
    (smallSumToCover U V hUV) (smallChainsInclusion ℚ (TopCat.of X) (twoSetCover U V hUV))

end TernaryPoly.RationalRelativeSupport
