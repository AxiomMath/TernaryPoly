module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePositiveIntegrability
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.SphericalPlaneContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineFinitePadicIntegrand_global_integrable (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (exponent : ℂ) (convergent : 3 < exponent.re) :
    Integrable (goodLineFinitePadicIntegrand cusp vector exponent)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  obtain ⟨bound, bounded⟩ := cusp.bounded vector
  apply ((goodLinePositiveWeight_integrable exponent convergent).mul_const bound).mono'
    (goodLineFinitePadicIntegrand_continuous cusp vector spherical exponent).aestronglyMeasurable
  filter_upwards [] with pair
  change ‖normPower (GeneralLinearGroup.det (atFinite (standardGoodLineFinitePadicCoordinates pair).block)) exponent *
    cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates pair).block)‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)

theorem goodLineFiniteVectorIntegrand_integrable (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + parameter).re) :
    Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  exact (goodLineFinitePadicIntegrand_global_integrable cusp vector spherical _ convergent).congr
    (Filter.Eventually.of_forall (fun finite =>
      (goodLineFinitePadicIntegrand_eq degree cusp parameter vector spherical finite).symm))

theorem goodLineFiniteVectorIntegrand_endpoint_integrable (degree : ℕ) (large : 3 < degree)
    (cusp : CuspidalRepresentation) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    Integrable (fun finite => standardGoodLineFiniteCuspWeight degree cohomologicalPoint finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  apply goodLineFiniteVectorIntegrand_integrable degree cusp cohomologicalPoint vector spherical
  have degree_large : (3 : ℝ) < degree := by exact_mod_cast large
  norm_num [cohomologicalPoint, Complex.add_re, Complex.div_re]
  linarith

end TernaryPeriodPolynomials.SphericalDetection.Helpers
