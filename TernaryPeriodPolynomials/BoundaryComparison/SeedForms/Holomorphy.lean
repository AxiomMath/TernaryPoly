module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PieceToForm

@[expose] public section


/-!
# Holomorphy of the scalar weighted realization at every base (for the Eichler input of a cohomological datum)

Formalized by Claude Sonnet 5.5.  Combines `cuspScalarWeightedRealization_holomorphicWt` (any base, level-3-fixed vector)
with the `Wt`/plain bridge of `CuspidalSpan/PieceToForm`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction (EichlerInput)
open TernaryPeriodPolynomials.EdgeControl (spherical_fixed)
open TernaryPeriodPolynomials.LevelThreeSource (levelThreeStages)
open TernaryPeriodPolynomials.EvenLevelThree
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.CuspidalSpan

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

/-- **Holomorphy of the scalar weighted realization at EVERY adelic base point** (in particular at `1 · b_F(1)` and `J · b_F(1)`), for the vector of an
`EichlerInput` of a cohomological datum. -/
theorem scalar_holomorphic_allBases {σ : CuspidalRepresentation} {n : ℕ} (I : EichlerInput σ n) (coh : Cohomological σ n)
    (base : BinaryAdelicGL) :
    DifferentiableOn ℂ (cuspScalarWeightedRealization σ I.halfWeight I.vector base) {z : ℂ | 0 < z.im} := by
  have fixed : I.vector.val ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence :=
    spherical_fixed σ I.vector.val I.vector_spherical
  have stages := levelThreeStages coh
  have holoWt : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt σ (2 * I.halfWeight) I.vector.val)
      UpperHalfPlane.upperHalfPlaneSet :=
    holomorphicOrbitWt_of_holomorphicOrbit σ I.halfWeight I.vector.val I.holomorphic
  have h := cuspScalarWeightedRealization_holomorphicWt σ stages (2 * I.halfWeight) I.vector fixed holoWt base
  exact h.congr fun point hpoint =>
    (cuspScalarWeightedRealizationWt_two_mul σ I.halfWeight I.vector base point hpoint).symm

end TernaryPeriodPolynomials.Argument.FormSeedBridge
