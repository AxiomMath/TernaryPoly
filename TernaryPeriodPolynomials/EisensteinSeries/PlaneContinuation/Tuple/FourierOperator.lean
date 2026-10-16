module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AdmissibleRealAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdmissibleRealAction TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleFourierOperator

def projection {degree : ℕ} (data : InducingData degree) (index : ℤ) : Space data →L[ℂ] Space data :=
  ContinuousLinearMap.pi (fun key => (RotationFourier.modeOperator data.cusp index).comp (ContinuousLinearMap.proj key))

theorem projection_apply {degree : ℕ} (data : InducingData degree) (index : ℤ) (value : Space data)
    (key : UniversalFiniteProfiles.Key data) :
    projection data index value key = RotationFourier.modeVector data.cusp index (value key) := rfl

def integrand {degree : ℕ} (data : InducingData degree) (index : ℤ) (value : Space data)
    (parameter : RotationCircle.Parameter) : Space data :=
  fourier (-index) parameter • action data (RotationCircle.rotation parameter) value

theorem integrand_integrable {degree : ℕ} (data : InducingData degree) (index : ℤ) (value : Space data) :
    Integrable (integrand data index value) AddCircle.haarAddCircle := by
  have continuous : Continuous (integrand data index value) :=
    (fourier (-index)).continuous.smul (continuous_pi (fun key => RotationFourier.orbit_continuous data.cusp (value key)))
  exact continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem projection_integral {degree : ℕ} (data : InducingData degree) (index : ℤ) (value : Space data) :
    projection data index value = ∫ parameter, integrand data index value parameter ∂AddCircle.haarAddCircle := by
  funext key
  exact (ContinuousLinearMap.proj key : Space data →L[ℂ] data.cusp.H).integral_comp_comm (integrand_integrable data index value)

theorem row_action {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (matrix : BinaryRealGL) (value : Space data) :
    TupleRecoveryOperator.row data parameter halfPlane point (action data matrix value) =
      data.cusp.π (atInfinity matrix) (TupleRecoveryOperator.row data parameter halfPlane point value) := by
  simp only [TupleRecoveryOperator.row_apply, AdmissibleRealAction.action_apply, RecoveryCoefficients.operator,
    FiniteHilbertConvolution.operator_real, map_sum]

theorem projectedRow_action {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (matrix : BinaryRealGL) (value : Space data) :
    TupleRecoveryOperator.projectedRow data parameter halfPlane point (action data matrix value) =
      data.cusp.π (atInfinity matrix) (TupleRecoveryOperator.projectedRow data parameter halfPlane point value) := by
  simp only [TupleRecoveryOperator.projectedRow, ContinuousLinearMap.comp_apply, row_action,
    AveragingSmooth.averagingOperator_real]

theorem averagedRow_action {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) (matrix : BinaryRealGL) (value : Space data) :
    TupleRecoveryOperator.averagedRow data parameter halfPlane point (action data matrix value) =
      data.cusp.π (atInfinity matrix) (TupleRecoveryOperator.averagedRow data parameter halfPlane point value) := by
  simp only [TupleRecoveryOperator.averagedRow, _root_.smul_apply, _root_.sum_apply,
    projectedRow_action, map_smul, map_sum]

theorem recovery_action {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (matrix : BinaryRealGL) (value : Space data) :
    TupleRecoveryOperator.operator data parameter halfPlane (action data matrix value) =
      action data matrix (TupleRecoveryOperator.operator data parameter halfPlane value) := by
  funext key
  exact averagedRow_action data parameter halfPlane (UniversalFiniteProfiles.representative data key) matrix value

theorem projection_recovery {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (index : ℤ) (value : Space data) :
    projection data index (TupleRecoveryOperator.operator data parameter halfPlane value) =
      TupleRecoveryOperator.operator data parameter halfPlane (projection data index value) := by
  rw [projection_integral, projection_integral,
    ← (TupleRecoveryOperator.operator data parameter halfPlane).integral_comp_comm (integrand_integrable data index value)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro point
  simp only [integrand, map_smul, recovery_action]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleFourierOperator
