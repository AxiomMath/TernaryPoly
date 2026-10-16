module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportSmallUnion

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SphereOddDegree RationalRelativeExcision RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- The actual supported-chain quotient is isomorphic to literal relative singular chains. -/
def supportedRelativeIso (S : Set X) : cokernel (supportedInclusion S) ≅ relativeChains S :=
  cokernel.mapIso (supportedInclusion S) (inclusion S)
    (asIso (subChainCorestrict ℚ (TopCat.of X) S)).symm (Iso.refl _) (by
      apply (cancel_epi (subChainCorestrict ℚ (TopCat.of X) S)).mp
      simp only [Iso.symm_hom, asIso_inv, ← Category.assoc,
        IsIso.hom_inv_id, Category.id_comp]
      exact corestrict_supportedInclusion S)

/-- The comparison preserves the actual absolute-to-relative quotient projection. -/
theorem supportedRelativeIso_projection (S : Set X) :
    cokernel.π (supportedInclusion S) ≫ (supportedRelativeIso S).hom = cokernel.π (inclusion S) := by
  simp [supportedRelativeIso, cokernel.mapIso, cokernel.map]

/-- The actual quotient by small chains maps to the literal quotient by all union chains. -/
def smallRelativeComparison (U V : Set X) :
    cokernel (supportedSmallSumInclusion U V) ⟶ relativeChains (U ∪ V) :=
  cokernel.map (supportedSmallSumInclusion U V) (supportedInclusion (U ∪ V))
    (smallSumToUnion U V) (𝟙 _) (by simpa using (smallSumToUnion_inclusion U V).symm) ≫
      (supportedRelativeIso (U ∪ V)).hom

/-- The actual small relative comparison preserves the literal quotient projection. -/
theorem smallRelativeComparison_projection (U V : Set X) :
    cokernel.π (supportedSmallSumInclusion U V) ≫ smallRelativeComparison U V =
      cokernel.π (inclusion (U ∪ V)) := by
  simp only [smallRelativeComparison, cokernel.map, cokernel.π_desc_assoc, Category.id_comp]
  exact supportedRelativeIso_projection (U ∪ V)

/-- Open excision gives a genuine quasi-isomorphism from small relative chains to literal relative chains. -/
theorem smallRelativeComparison_quasiIso (U V : TopologicalSpace.Opens X) :
    QuasiIso (smallRelativeComparison (U : Set X) (V : Set X)) := by
  have : QuasiIso (smallSumToUnion (U : Set X) (V : Set X)) := smallSumToUnion_quasiIso U V
  have : QuasiIso (cokernel.map (supportedSmallSumInclusion (U : Set X) (V : Set X))
      (supportedInclusion ((U : Set X) ∪ V)) (smallSumToUnion (U : Set X) (V : Set X))
      (𝟙 _) (by simpa using (smallSumToUnion_inclusion (U : Set X) (V : Set X)).symm)) :=
    RelativeExcisionAlgebra.cokernel_map_quasiIso _ _ _ _ _
  unfold smallRelativeComparison
  infer_instance

end TernaryPoly.RationalRelativeSupport
