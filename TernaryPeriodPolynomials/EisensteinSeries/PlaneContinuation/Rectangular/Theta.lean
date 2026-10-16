module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.Frames

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta

noncomputable def matrixTerm (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) : ℂ :=
  test (point⁻¹.val * matrix.map rationalAdele * binary.val)

noncomputable def fullTheta (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) : ℂ := ∑' matrix : Rectangular ℚ, matrixTerm test point binary matrix

noncomputable def singularTheta (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) : ℂ :=
  ∑' matrix : {matrix : Rectangular ℚ // ¬ FullRank matrix}, matrixTerm test point binary matrix.val

theorem decomposition (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (summable : Summable (matrixTerm test point binary)) :
    fullTheta test point binary = RectangularKernel.theta test point binary + singularTheta test point binary :=
  (summable.tsum_subtype_add_tsum_subtype_compl {matrix | FullRank matrix}).symm

def leftEquiv (rational : RationalGL3) : Rectangular ℚ ≃ Rectangular ℚ where
  toFun matrix := rational.val * matrix
  invFun matrix := rational⁻¹.val * matrix
  left_inv matrix := by
    change rational⁻¹.val * (rational.val * matrix) = matrix
    have inverse : rational⁻¹.val * rational.val = 1 := rational.inv_val
    rw [← Matrix.mul_assoc, inverse, Matrix.one_mul]
  right_inv matrix := by
    change rational.val * (rational⁻¹.val * matrix) = matrix
    have inverse : rational.val * rational⁻¹.val = 1 := rational.val_inv
    rw [← Matrix.mul_assoc, inverse, Matrix.one_mul]

def rightEquiv (rational : BinaryRationalGL) : Rectangular ℚ ≃ Rectangular ℚ where
  toFun matrix := matrix * rational.val
  invFun matrix := matrix * rational⁻¹.val
  left_inv matrix := by
    change (matrix * rational.val) * rational⁻¹.val = matrix
    have inverse : rational.val * rational⁻¹.val = 1 := rational.val_inv
    rw [Matrix.mul_assoc, inverse, Matrix.mul_one]
  right_inv matrix := by
    change (matrix * rational⁻¹.val) * rational.val = matrix
    have inverse : rational⁻¹.val * rational.val = 1 := rational.inv_val
    rw [Matrix.mul_assoc, inverse, Matrix.mul_one]

theorem matrixTerm_rational_left (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) (rational : RationalGL3) (matrix : Rectangular ℚ) :
    matrixTerm test (rationalGroup rational * point) binary matrix =
      matrixTerm test point binary (leftEquiv rational⁻¹ matrix) := by
  unfold matrixTerm
  change test ((rationalGroup rational * point)⁻¹.val * matrix.map rationalAdele * binary.val) =
    test (point⁻¹.val * (rational⁻¹.val * matrix).map rationalAdele * binary.val)
  rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, Matrix.map_mul]
  change test ((point⁻¹.val * (rationalGroup rational⁻¹).val) * matrix.map rationalAdele * binary.val) = _
  simp only [Matrix.mul_assoc]
  rfl

theorem matrixTerm_rational_binary (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) (rational : BinaryRationalGL) (matrix : Rectangular ℚ) :
    matrixTerm test point (GeneralLinearGroup.map rationalAdele rational * binary) matrix =
      matrixTerm test point binary (rightEquiv rational matrix) := by
  unfold matrixTerm
  change test (point⁻¹.val * matrix.map rationalAdele *
      (GeneralLinearGroup.map rationalAdele rational * binary).val) =
    test (point⁻¹.val * (matrix * rational.val).map rationalAdele * binary.val)
  rw [Units.val_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rfl

theorem fullTheta_rational_left (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) (rational : RationalGL3) :
    fullTheta test (rationalGroup rational * point) binary = fullTheta test point binary := by
  simp only [fullTheta, matrixTerm_rational_left]
  exact (leftEquiv rational⁻¹).tsum_eq _

theorem fullTheta_rational_binary (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) (rational : BinaryRationalGL) :
    fullTheta test point (GeneralLinearGroup.map rationalAdele rational * binary) = fullTheta test point binary := by
  simp only [fullTheta, matrixTerm_rational_binary]
  exact (rightEquiv rational).tsum_eq _

theorem matrixTerm_stabilizer (test : Rectangular Adeles → ℂ) (point : AdelicGL)
    (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (parameter : Adeles) :
    matrixTerm test point (SingularFrames.stabilizer basis parameter * binary) matrix =
      matrixTerm test point binary matrix := by
  unfold matrixTerm
  rw [Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_assoc point⁻¹.val,
    SingularFrames.stabilizer_fixed matrix basis zeroFirst]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
