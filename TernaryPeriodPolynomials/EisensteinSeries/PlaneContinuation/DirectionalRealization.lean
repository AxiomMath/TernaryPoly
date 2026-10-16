module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.ScalarDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarDerivative
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization

noncomputable def smoothTranslate (data : CuspidalRepresentation) (matrix : BinaryRealGL) :
    data.smooth →ₗ[ℂ] data.smooth where
  toFun vector := ⟨data.π (atInfinity matrix) vector.val, data.smooth_stable _ _ vector.property⟩
  map_add' first second := Subtype.ext (map_add _ first.val second.val)
  map_smul' scalar vector := Subtype.ext (map_smul _ scalar vector.val)

theorem smoothTranslate_realize (data : CuspidalRepresentation) (matrix : BinaryRealGL)
    (vector : data.smooth) (point : BinaryAdelicGL) :
    data.realize (smoothTranslate data matrix vector) point =
      data.realize vector (point * atInfinity matrix) := data.equivariant _ vector point

theorem directionalOperator_translate (data : CuspidalRepresentation) (matrix : BinaryRealGL)
    (vector : data.smooth) (direction : BinaryMatrix) :
    directionalOperator data direction (smoothTranslate data matrix vector) =
      smoothTranslate data matrix (directionalOperator data (conjugation matrix direction) vector) := by
  let operator := (unitaryOperator data (atInfinity matrix)).restrictScalars ℝ
  have differentiability : DifferentiableAt ℝ (realOrbit data vector.val) 1 :=
    (smooth_orbit_contDiffAt_one data vector).differentiableAt (by simp)
  have derivativeAtConjugate : HasFDerivAt (realOrbit data vector.val)
      (fderiv ℝ (realOrbit data vector.val) 1) (conjugation matrix 1) := by
    rw [conjugation_one]
    exact differentiability.hasFDerivAt
  have derivative := operator.hasFDerivAt.comp 1
    (derivativeAtConjugate.comp 1 (conjugation matrix).hasFDerivAt)
  have equality : operator ∘ (realOrbit data vector.val ∘ conjugation matrix) =
      realOrbit data (smoothTranslate data matrix vector).val := by
    funext value
    exact (realOrbit_translate data vector.val matrix value).symm
  rw [equality] at derivative
  apply Subtype.ext
  exact congrArg (fun linear : BinaryMatrix →L[ℝ] data.H => linear direction) derivative.fderiv

noncomputable def directionalSmooth (data : CuspidalRepresentation) (vector : data.smooth) :
    BinaryMatrix →ₗ[ℝ] data.smooth where
  toFun direction := directionalOperator data direction vector
  map_add' first second := Subtype.ext (map_add (fderiv ℝ (realOrbit data vector.val) 1) first second)
  map_smul' scalar direction := Subtype.ext (map_smul (fderiv ℝ (realOrbit data vector.val) 1) scalar direction)

noncomputable def realizedDirectional (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) : BinaryMatrix →ₗ[ℝ] ℂ :=
  (((LinearMap.proj point).comp data.realize).restrictScalars ℝ).comp (directionalSmooth data vector)

noncomputable def scalarDirectional (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) : BinaryMatrix →L[ℝ] ℂ :=
  fderiv ℝ (scalarMatrixOrbit data point vector) 1

theorem scalarMatrixOrbit_translate (data : CuspidalRepresentation) (matrix : BinaryRealGL)
    (point : BinaryAdelicGL) (vector : data.smooth) (value : BinaryMatrix) :
    scalarMatrixOrbit data point (smoothTranslate data matrix vector) value =
      scalarMatrixOrbit data (point * atInfinity matrix) vector (conjugation matrix value) := by
  unfold scalarMatrixOrbit
  rw [smoothTranslate_realize, invertibleMatrix_conjugation,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
  have inverseEquality : atInfinity matrix⁻¹ = (atInfinity matrix)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, mul_inv_cancel, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one]
  rw [inverseEquality]
  group

theorem scalarDirectional_translate (data : CuspidalRepresentation) (matrix : BinaryRealGL)
    (point : BinaryAdelicGL) (vector : data.smooth) (direction : BinaryMatrix) :
    scalarDirectional data point (smoothTranslate data matrix vector) direction =
      scalarDirectional data (point * atInfinity matrix) vector (conjugation matrix direction) := by
  have membership : (1 : BinaryMatrix) ∈ binaryDomain := by simp [binaryDomain]
  have differentiability := (((scalarMatrixOrbit_contDiffOn data (point * atInfinity matrix) vector)
    1 membership).contDiffAt (binaryDomain_isOpen.mem_nhds membership)).differentiableAt (by simp)
  have derivativeAtConjugate : HasFDerivAt (scalarMatrixOrbit data (point * atInfinity matrix) vector)
      (scalarDirectional data (point * atInfinity matrix) vector) (conjugation matrix 1) := by
    rw [conjugation_one]
    exact differentiability.hasFDerivAt
  have derivative := derivativeAtConjugate.comp 1 (conjugation matrix).hasFDerivAt
  have equality : scalarMatrixOrbit data (point * atInfinity matrix) vector ∘ conjugation matrix =
      scalarMatrixOrbit data point (smoothTranslate data matrix vector) := by
    funext value
    exact (scalarMatrixOrbit_translate data matrix point vector value).symm
  rw [equality] at derivative
  exact congrArg (fun linear : BinaryMatrix →L[ℝ] ℂ => linear direction) derivative.fderiv

theorem scalarDirectional_generator (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) :
    scalarDirectional data point vector generator = realizedDirectional data point vector generator := by
  change fderiv ℝ (scalarMatrixOrbit data point vector) 1 generator =
    data.realize (rotationDerivative data vector) point
  have equality := congrFun (scalarTangent_eq_realize data point vector) 0
  simpa only [scalarTangent, rotation_zero, Matrix.GeneralLinearGroup.coe_one, one_mul,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, mul_one] using equality

/-- Scalar realization commutes with differentiation in every conjugate rotation direction. -/
theorem scalarDirectional_conjugateGenerator (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (matrix : BinaryRealGL) :
    scalarDirectional data point vector (conjugation matrix generator) =
      realizedDirectional data point vector (conjugation matrix generator) := by
  have equality := scalarDirectional_generator data (point * (atInfinity matrix)⁻¹)
    (smoothTranslate data matrix vector)
  rw [scalarDirectional_translate, inv_mul_cancel_right] at equality
  change scalarDirectional data point vector (conjugation matrix generator) =
    data.realize (directionalOperator data generator (smoothTranslate data matrix vector))
      (point * (atInfinity matrix)⁻¹) at equality
  rw [directionalOperator_translate, smoothTranslate_realize, inv_mul_cancel_right] at equality
  exact equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
