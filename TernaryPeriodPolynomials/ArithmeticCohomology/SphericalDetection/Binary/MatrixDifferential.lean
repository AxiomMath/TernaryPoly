module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationProjection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineCoefficientDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspMatrixOrbit (cusp : CuspidalRepresentation) (vector : cusp.H) (matrix : BinaryRealMatrix) : cusp.H :=
  cusp.π (atInfinity (invertibleMatrix matrix)) vector

def cuspMatrixDifferential (cusp : CuspidalRepresentation) (vector : cusp.H) : BinaryRealMatrix →L[ℝ] cusp.H :=
  fderiv ℝ (cuspMatrixOrbit cusp vector) 1

theorem cuspMatrixOrbit_smooth_differentiable (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    DifferentiableAt ℝ (cuspMatrixOrbit cusp vector.val) 1 := by
  have regular := smooth_one_contDiffOn (function := fun matrix => cusp.π (atInfinity matrix) vector.val)
    ((cusp.smooth_exact vector.val).mp vector.property).1
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  exact (regular.contDiffAt (domain_open.mem_nhds (by simp))).differentiableAt (by simp)

def binaryMatrixLine (direction : BinaryRealMatrix) (parameter : ℝ) : BinaryRealMatrix :=
  1 + parameter • direction

theorem binaryMatrixLine_contDiff (direction : BinaryRealMatrix) {order : WithTop ℕ∞} :
    ContDiff ℝ order (binaryMatrixLine direction) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

theorem binaryMatrixLine_hasDerivAt (direction : BinaryRealMatrix) :
    HasDerivAt (binaryMatrixLine direction) direction 0 := by
  convert ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add (1 : BinaryRealMatrix) using 1 <;>
    first | rfl | simp

theorem binaryMatrixLine_eventually_invertible (direction : BinaryRealMatrix) :
    ∀ᶠ parameter : ℝ in nhds 0, (binaryMatrixLine direction parameter).det ≠ 0 := by
  have open_domain : IsOpen {parameter : ℝ | (binaryMatrixLine direction parameter).det ≠ 0} :=
    isOpen_ne_fun ((binaryMatrixLine_contDiff direction (order := 1)).continuous.matrix_det) continuous_const
  exact open_domain.mem_nhds (by simp [binaryMatrixLine])

theorem cuspMatrixDifferential_curve (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) 1) (direction : BinaryRealMatrix) :
    HasDerivAt (fun parameter => cuspMatrixOrbit cusp vector (binaryMatrixLine direction parameter))
      (cuspMatrixDifferential cusp vector direction) 0 := by
  have derivative := regular.hasFDerivAt.comp_hasDerivAt_of_eq 0 (binaryMatrixLine_hasDerivAt direction)
    (by simp [binaryMatrixLine])
  convert derivative using 1 <;> rfl

theorem binaryMatrixLine_conjugation (matrix : BinaryRealGL) (direction : BinaryRealMatrix) (parameter : ℝ) :
    binaryMatrixLine direction parameter * matrix.val =
      matrix.val * binaryMatrixLine (matrix⁻¹.val * direction * matrix.val) parameter := by
  simp only [binaryMatrixLine, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, ← mul_assoc, matrix.mul_inv, one_mul]

theorem cuspMatrixDifferential_translate (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (matrix : BinaryRealGL) (direction : BinaryRealMatrix) :
    cuspMatrixDifferential cusp (cusp.π (atInfinity matrix) vector.val) direction =
      cusp.π (atInfinity matrix) (cuspMatrixDifferential cusp vector.val (matrix⁻¹.val * direction * matrix.val)) := by
  let translated : cusp.smooth := ⟨cusp.π (atInfinity matrix) vector.val, cusp.smooth_stable _ _ vector.property⟩
  let conjugated := matrix⁻¹.val * direction * matrix.val
  have left := cuspMatrixDifferential_curve cusp translated.val
    (cuspMatrixOrbit_smooth_differentiable cusp translated) direction
  have right := ((cuspUnitaryOperator cusp (atInfinity matrix)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (cuspMatrixDifferential_curve cusp vector.val (cuspMatrixOrbit_smooth_differentiable cusp vector) conjugated)
  have equality : (fun parameter => cuspMatrixOrbit cusp translated.val (binaryMatrixLine direction parameter)) =ᶠ[nhds 0]
      (fun parameter => cusp.π (atInfinity matrix) (cuspMatrixOrbit cusp vector.val (binaryMatrixLine conjugated parameter))) := by
    filter_upwards [binaryMatrixLine_eventually_invertible direction, binaryMatrixLine_eventually_invertible conjugated]
      with parameter invertible conjugated_invertible
    have group_equality : invertibleMatrix (binaryMatrixLine direction parameter) * matrix =
        matrix * invertibleMatrix (binaryMatrixLine conjugated parameter) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, invertibleMatrix_val _ invertible,
        invertibleMatrix_val _ conjugated_invertible]
      exact binaryMatrixLine_conjugation matrix direction parameter
    change (cusp.π (atInfinity (invertibleMatrix (binaryMatrixLine direction parameter))) * cusp.π (atInfinity matrix)) vector.val =
      (cusp.π (atInfinity matrix) * cusp.π (atInfinity (invertibleMatrix (binaryMatrixLine conjugated parameter)))) vector.val
    rw [← map_mul, ← map_mul, ← atInfinity_mul, ← atInfinity_mul, group_equality]
  exact left.unique (right.congr_of_eventuallyEq equality)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
