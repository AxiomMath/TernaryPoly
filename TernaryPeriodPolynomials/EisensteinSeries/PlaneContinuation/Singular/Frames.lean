module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.Absolute

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularFrames

theorem minor_zero {field : Type*} [Field field] (matrix : Rectangular field)
    (singular : ¬ FullRank matrix) (first second : Fin 3) :
    matrix first 0 * matrix second 1 - matrix first 1 * matrix second 0 = 0 := by
  have vanishing : exterior matrix = 0 := not_ne_iff.mp singular
  have zero0 := congrFun vanishing 0
  have zero1 := congrFun vanishing 1
  have zero2 := congrFun vanishing 2
  simp [exterior, crossProduct] at zero0 zero1 zero2
  fin_cases first <;> fin_cases second
  · ring
  · change matrix 0 0 * matrix 1 1 - matrix 0 1 * matrix 1 0 = 0
    linear_combination zero2
  · change matrix 0 0 * matrix 2 1 - matrix 0 1 * matrix 2 0 = 0
    linear_combination -zero1
  · change matrix 1 0 * matrix 0 1 - matrix 1 1 * matrix 0 0 = 0
    linear_combination -zero2
  · ring
  · change matrix 1 0 * matrix 2 1 - matrix 1 1 * matrix 2 0 = 0
    linear_combination zero0
  · change matrix 2 0 * matrix 0 1 - matrix 2 1 * matrix 0 0 = 0
    linear_combination zero1
  · change matrix 2 0 * matrix 1 1 - matrix 2 1 * matrix 1 0 = 0
    linear_combination -zero0
  · ring

theorem exists_zero_first_column {field : Type*} [Field field] (matrix : Rectangular field)
    (singular : ¬ FullRank matrix) :
    ∃ basis : GeneralLinearGroup (Fin 2) field, ∀ row, (matrix * basis.val) row 0 = 0 := by
  classical
  by_cases vanishing : ∀ row, matrix row 0 = 0
  · exact ⟨1, by simpa only [Units.val_one, Matrix.mul_one] using vanishing⟩
  push Not at vanishing
  obtain ⟨pivot, nonzero⟩ := vanishing
  let basisMatrix : Matrix (Fin 2) (Fin 2) field := !![matrix pivot 1, 1; -matrix pivot 0, 0]
  have determinant : basisMatrix.det ≠ 0 := by
    simpa [basisMatrix, Matrix.det_fin_two] using nonzero
  refine ⟨GeneralLinearGroup.mkOfDetNeZero basisMatrix determinant, ?_⟩
  intro row
  change (matrix * basisMatrix) row 0 = 0
  simp [basisMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination minor_zero matrix singular row pivot

theorem zero_first_column_fixed {ring : Type*} [CommRing ring] (matrix : Rectangular ring)
    (zeroFirst : ∀ row, matrix row 0 = 0) (parameter : ring) :
    matrix * (binaryUnipotent parameter).val = matrix := by
  ext row column
  fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two, binaryUnipotent, zeroFirst]

noncomputable def stabilizer (basis : BinaryRationalGL) (parameter : Adeles) : BinaryAdelicGL :=
  GeneralLinearGroup.map rationalAdele basis * binaryUnipotent parameter *
    (GeneralLinearGroup.map rationalAdele basis)⁻¹

theorem unipotent_det {ring : Type*} [CommRing ring] (parameter : ring) :
    GeneralLinearGroup.det (binaryUnipotent parameter) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, binaryUnipotent, Matrix.det_fin_two]

theorem stabilizer_det (basis : BinaryRationalGL) (parameter : Adeles) :
    GeneralLinearGroup.det (stabilizer basis parameter) = 1 := by
  simp [stabilizer, map_mul, unipotent_det]

theorem stabilizer_fixed (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (parameter : Adeles) :
    matrix.map rationalAdele * (stabilizer basis parameter).val = matrix.map rationalAdele := by
  have mappedZero : ∀ row, ((matrix * basis.val).map rationalAdele) row 0 = 0 := by
    intro row
    change rationalAdele ((matrix * basis.val) row 0) = 0
    rw [zeroFirst, map_zero]
  have fixed := zero_first_column_fixed ((matrix * basis.val).map rationalAdele) mappedZero parameter
  rw [Matrix.map_mul] at fixed
  change (matrix.map rationalAdele * (GeneralLinearGroup.map rationalAdele basis).val) *
    (binaryUnipotent parameter).val = matrix.map rationalAdele * (GeneralLinearGroup.map rationalAdele basis).val at fixed
  have inverse : (GeneralLinearGroup.map rationalAdele basis).val *
      (GeneralLinearGroup.map rationalAdele basis)⁻¹.val = 1 :=
    (GeneralLinearGroup.map rationalAdele basis).val_inv
  simp only [stabilizer, Units.val_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, fixed, Matrix.mul_assoc,
    inverse, Matrix.mul_one]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularFrames
