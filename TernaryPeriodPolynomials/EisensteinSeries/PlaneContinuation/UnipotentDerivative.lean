module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MeanZeroBound

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentPeriodicity TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarDerivative TernaryPeriodPolynomials.PlaneEisensteinContinuation.SupNormOrbit
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentDerivative

def generator : BinaryMatrix := !![0, 1; 0, 0]

theorem upper_hasDerivAt (parameter : ℝ) :
    HasDerivAt (fun parameter : ℝ => (binaryUnipotent parameter).val) generator parameter := by
  apply hasDerivAt_pi.mpr
  intro row
  apply hasDerivAt_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;>
    first | exact hasDerivAt_const parameter _ | exact hasDerivAt_id parameter

theorem upper_inv_generator (parameter : ℝ) : (binaryUnipotent parameter)⁻¹.val * generator = generator := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUnipotent, generator, Matrix.mul_apply, Fin.sum_univ_two]

theorem product_inv_tangent (parameter : ℝ) (realPoint : BinaryRealGL) :
    (binaryUnipotent parameter * realPoint)⁻¹.val * (generator * realPoint.val) =
      realPoint⁻¹.val * generator * realPoint.val := by
  rw [_root_.mul_inv_rev, Units.val_mul, mul_assoc, ← mul_assoc (binaryUnipotent parameter)⁻¹.val,
    upper_inv_generator, ← mul_assoc]

theorem realFunction_hasDerivAt {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (point : BinaryLevel.IntegralBinaryGL) (realPoint : BinaryRealGL) (parameter : ℝ) :
    HasDerivAt (realFunction data.cusp vector point realPoint)
      (realFunction data.cusp (directionalOperator data.cusp (realPoint⁻¹.val * generator * realPoint.val) vector)
        point realPoint parameter) parameter := by
  let basePoint := atFinite (GeneralLinearGroup.map integralEmbedding point)
  have curveDerivative : HasDerivAt (fun parameter : ℝ => (binaryUnipotent parameter).val * realPoint.val)
      (generator * realPoint.val) parameter := by
    apply hasDerivAt_pi.mpr
    intro row
    apply hasDerivAt_pi.mpr
    intro column
    change HasDerivAt (fun parameter => ∑ index : Fin 2, (binaryUnipotent parameter).val row index * realPoint.val index column)
      (∑ index : Fin 2, generator row index * realPoint.val index column) parameter
    exact HasDerivAt.fun_sum (fun index _ =>
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp (upper_hasDerivAt parameter) row) index)).mul_const _)
  have derivative := (scalarMatrixOrbit_differentiableAt data.cusp basePoint vector
    (binaryUnipotent parameter * realPoint)).hasFDerivAt.comp_hasDerivAt parameter curveDerivative
  have functionEquality : scalarMatrixOrbit data.cusp basePoint vector ∘
      (fun parameter : ℝ => (binaryUnipotent parameter).val * realPoint.val) =
      realFunction data.cusp vector point realPoint := by
    funext parameter
    change data.cusp.realize vector (basePoint * atInfinity (invertibleMatrix (binaryUnipotent parameter * realPoint).val)) = _
    rw [invertibleMatrix_units]
    rfl
  change HasDerivAt (scalarMatrixOrbit data.cusp basePoint vector ∘
    (fun parameter : ℝ => (binaryUnipotent parameter).val * realPoint.val)) _ parameter at derivative
  rw [functionEquality] at derivative
  have valueEquality := scalarMatrixOrbit_fderiv data basePoint vector
    (binaryUnipotent parameter * realPoint) (generator * realPoint.val)
  rw [product_inv_tangent] at valueEquality
  convert derivative using 1
  exact valueEquality.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentDerivative
