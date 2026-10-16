module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CohomologicalCasimir

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarDerivative TernaryPeriodPolynomials.PlaneEisensteinContinuation.SupNormOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart

noncomputable def direction : ℂ →L[ℝ] BinaryMatrix :=
  let linear : ℂ →ₗ[ℝ] BinaryMatrix :=
    { toFun := fun value => !![value.im, value.re; 0, 0]
      map_add' := by intros; ext row column; fin_cases row <;> fin_cases column <;> simp
      map_smul' := by intros; ext row column; fin_cases row <;> fin_cases column <;> simp }
  ⟨linear, linear.continuous_of_finiteDimensional⟩

def matrix (point : ℂ) : BinaryMatrix := !![point.im, point.re; 0, 1]

theorem matrix_det (point : ℂ) : (matrix point).det = point.im := by simp [matrix, Matrix.det_fin_two]

noncomputable def unit (point : ℂ) (positive : 0 < point.im) : BinaryRealGL :=
  ⟨matrix point, !![point.im⁻¹, -point.re / point.im; 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [ne_of_gt positive]
    ring, by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [ne_of_gt positive]
    ring⟩

theorem matrix_hasFDerivAt (point : ℂ) : HasFDerivAt matrix direction point := by
  have equality : matrix = fun value => direction value + !![0, 0; 0, 1] := by
    funext value
    ext row column
    fin_cases row <;> fin_cases column <;> simp [matrix, direction]
  rw [equality]
  exact direction.hasFDerivAt.add_const _

theorem inverse_direction_one (point : ℂ) (positive : 0 < point.im) :
    (unit point positive)⁻¹.val * direction 1 =
      (2 * point.im)⁻¹ • (symmetricMatrix - rotationMatrix) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [unit, direction, symmetricMatrix, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

theorem inverse_direction_I (point : ℂ) (positive : 0 < point.im) :
    (unit point positive)⁻¹.val * direction Complex.I =
      (2 * point.im)⁻¹ • ((1 : BinaryMatrix) + diagonalMatrix) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [unit, direction, diagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

noncomputable def raw (data : CuspidalRepresentation) (point : BinaryAdelicGL) (vector : data.smooth)
    (argument : ℂ) : ℂ := scalarMatrixOrbit data point vector (matrix argument)

theorem raw_eq (data : CuspidalRepresentation) (point : BinaryAdelicGL) (vector : data.smooth)
    (argument : ℂ) (positive : 0 < argument.im) :
    raw data point vector argument = data.realize vector (point * atInfinity (unit argument positive)) := by
  change data.realize vector (point * atInfinity (invertibleMatrix (unit argument positive).val)) = _
  rw [invertibleMatrix_units]

theorem raw_hasFDerivAt (data : CuspidalRepresentation) (point : BinaryAdelicGL) (vector : data.smooth)
    (argument : ℂ) (positive : 0 < argument.im) :
    HasFDerivAt (raw data point vector)
      ((fderiv ℝ (scalarMatrixOrbit data point vector) (matrix argument)).comp direction) argument :=
  (scalarMatrixOrbit_differentiableAt data point vector (unit argument positive)).hasFDerivAt.comp
    argument (matrix_hasFDerivAt argument)

theorem raw_fderiv {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (argument : ℂ) (positive : 0 < argument.im) (tangent : ℂ) :
    fderiv ℝ (raw data.cusp point vector) argument tangent =
      data.cusp.realize (directionalOperator data.cusp ((unit argument positive)⁻¹.val * direction tangent) vector)
        (point * atInfinity (unit argument positive)) := by
  have equality := congrArg (fun linear : ℂ →L[ℝ] ℂ => linear tangent)
    (raw_hasFDerivAt data.cusp point vector argument positive).fderiv
  change fderiv ℝ (raw data.cusp point vector) argument tangent =
    fderiv ℝ (scalarMatrixOrbit data.cusp point vector) (unit argument positive).val (direction tangent) at equality
  rw [equality, scalarMatrixOrbit_fderiv data]

theorem raw_fderiv_one {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (argument : ℂ) (positive : 0 < argument.im) :
    fderiv ℝ (raw data.cusp point vector) argument 1 =
      ((2 * argument.im)⁻¹ : ℝ) • data.cusp.realize (symmetricOperator data.cusp vector - rotationOperator data.cusp vector)
        (point * atInfinity (unit argument positive)) := by
  rw [raw_fderiv data point vector argument positive, inverse_direction_one, directionalOperator_real_smul,
    directionalOperator_sub]
  change data.cusp.realize ((((2 * argument.im)⁻¹ : ℝ) : ℂ) •
    (symmetricOperator data.cusp vector - rotationOperator data.cusp vector)) _ = _
  rw [map_smul]
  rfl

theorem raw_fderiv_I {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (argument : ℂ) (positive : 0 < argument.im) :
    fderiv ℝ (raw data.cusp point vector) argument Complex.I =
      ((2 * argument.im)⁻¹ : ℝ) • data.cusp.realize (diagonalOperator data.cusp vector)
        (point * atInfinity (unit argument positive)) := by
  rw [raw_fderiv data point vector argument positive, inverse_direction_I, directionalOperator_real_smul,
    directionalOperator_add]
  change data.cusp.realize ((((2 * argument.im)⁻¹ : ℝ) : ℂ) •
    (directionalOperator data.cusp 1 vector + diagonalOperator data.cusp vector)) _ = _
  rw [CentralDifferentiation.directionalOperator_identity, zero_add, map_smul]
  rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
