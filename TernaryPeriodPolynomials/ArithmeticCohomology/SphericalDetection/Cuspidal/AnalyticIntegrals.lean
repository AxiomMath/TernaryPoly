module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.IntervalIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.PartialDerivative
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DiskAverage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspSpherical_intervalIntegral_mem (cusp : CuspidalRepresentation) (vectors : ℝ → cusp.H)
    (continuous : Continuous vectors) (fixed : ∀ parameter, vectors parameter ∈ cuspSphericalValues cusp)
    (left right : ℝ) : (∫ parameter in left..right, vectors parameter) ∈ cuspSphericalValues cusp := by
  have integrable : IntervalIntegrable vectors volume left right := continuous.intervalIntegrable left right
  intro matrix
  change cuspUnitaryOperator cusp (atFinite (GeneralLinearGroup.map integralEmbedding matrix))
    (∫ parameter in left..right, vectors parameter) = _
  rw [← (cuspUnitaryOperator cusp (atFinite (GeneralLinearGroup.map integralEmbedding matrix))).intervalIntegral_comp_comm integrable]
  apply intervalIntegral.integral_congr
  intro parameter _
  exact fixed parameter matrix

theorem cuspSpherical_intervalIntegral_smooth (cusp : CuspidalRepresentation) (vectors : ℝ → cusp.H)
    (continuous : Continuous vectors) (fixed : ∀ parameter, vectors parameter ∈ cuspSphericalValues cusp)
    (analytic : ∀ center : ℝ, AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => cusp.π (atInfinity (invertibleMatrix point.1)) (vectors point.2)) (1, center))
    (left right : ℝ) : (∫ parameter in left..right, vectors parameter) ∈ cusp.smooth := by
  have integrable : IntervalIntegrable vectors volume left right := continuous.intervalIntegrable left right
  have spherical := cuspSpherical_intervalIntegral_mem cusp vectors continuous fixed left right
  apply cuspSpherical_smooth_of_analyticAt_one cusp _ spherical
  have integrated := analyticAt_intervalIntegral
    (fun point : BinaryRealMatrix × ℝ => cusp.π (atInfinity (invertibleMatrix point.1)) (vectors point.2))
    1 Set.univ isOpen_univ (Set.mem_univ _) (by
      intro matrix _
      exact (cuspUnitaryOperator cusp (atInfinity (invertibleMatrix matrix))).continuous.comp continuous)
    analytic left right
  apply integrated.congr
  filter_upwards [] with matrix
  exact (cuspUnitaryOperator cusp (atInfinity (invertibleMatrix matrix))).intervalIntegral_comp_comm integrable

theorem cuspSpherical_deriv_mem (cusp : CuspidalRepresentation) (vectors : ℝ → cusp.H) (center : ℝ)
    (regular : DifferentiableAt ℝ vectors center) (fixed : ∀ parameter, vectors parameter ∈ cuspSphericalValues cusp) :
    deriv vectors center ∈ cuspSphericalValues cusp := by
  intro matrix
  have applied := ((cuspUnitaryOperator cusp (atFinite (GeneralLinearGroup.map integralEmbedding matrix))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt center regular.hasDerivAt
  have equality : (fun parameter =>
      cuspUnitaryOperator cusp (atFinite (GeneralLinearGroup.map integralEmbedding matrix)) (vectors parameter)) = vectors :=
    funext (fun parameter => fixed parameter matrix)
  change HasDerivAt (fun parameter =>
    cuspUnitaryOperator cusp (atFinite (GeneralLinearGroup.map integralEmbedding matrix)) (vectors parameter)) _ center at applied
  rw [equality] at applied
  exact applied.unique regular.hasDerivAt

theorem cuspSpherical_deriv_smooth (cusp : CuspidalRepresentation) (vectors : ℝ → cusp.H) (center : ℝ)
    (regular : DifferentiableAt ℝ vectors center) (fixed : ∀ parameter, vectors parameter ∈ cuspSphericalValues cusp)
    (analytic : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => cusp.π (atInfinity (invertibleMatrix point.1)) (vectors point.2)) (1, center)) :
    deriv vectors center ∈ cusp.smooth := by
  have spherical := cuspSpherical_deriv_mem cusp vectors center regular fixed
  apply cuspSpherical_smooth_of_analyticAt_one cusp _ spherical
  have partial_derivative := analyticAt_partialDeriv
    (fun point : BinaryRealMatrix × ℝ => cusp.π (atInfinity (invertibleMatrix point.1)) (vectors point.2))
    1 center analytic
  apply partial_derivative.congr
  filter_upwards [] with matrix
  exact (((cuspUnitaryOperator cusp (atInfinity (invertibleMatrix matrix))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt center regular.hasDerivAt).deriv

end TernaryPeriodPolynomials.SphericalDetection.Helpers
