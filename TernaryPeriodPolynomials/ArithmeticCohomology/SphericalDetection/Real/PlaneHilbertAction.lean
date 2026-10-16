module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneCuspidalAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorSmoothCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneHilbertOperator {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) (element : RealPlaneGroup) :
    (index → cusp.H) →L[ℂ] (index → cusp.H) :=
  realPlaneCuspidalTwist degree element •
    (basisHilbertCoefficient cusp basis (realCoefficientComponent degree character (realPlaneMatrix element))).comp
      (binaryHilbertTranslation cusp (realPlaneBinaryInput element))

theorem realPlaneHilbertOperator_intertwines {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) (element : RealPlaneGroup)
    (values : realPlaneCuspidalRep degree cusp character) :
    cuspidalTensorHilbertEmbedding cusp basis ((realPlaneCuspidalRep degree cusp character).ρ element values) =
      realPlaneHilbertOperator degree cusp character basis element (cuspidalTensorHilbertEmbedding cusp basis values) := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  change cuspidalTensorValues cusp (HomogeneousPoly degree) at values
  change cuspidalTensorHilbertEmbedding cusp basis (realPlaneCuspidalTwist degree element •
    cuspidalTensorMap cusp (realCoefficientComponent degree character (realPlaneMatrix element))
      (cuspidalTensorTranslation cusp (realPlaneBinaryInput element) values)) = _
  rw [map_smul]
  rw [cuspidalTensorHilbertEmbedding_map, cuspidalTensorHilbertEmbedding_translation]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
