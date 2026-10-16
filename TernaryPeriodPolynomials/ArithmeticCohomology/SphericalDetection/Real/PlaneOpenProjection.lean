module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.RealPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineCuspidalPrismDefect

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneSchurBlock (matrix : RealGL3) : BinaryRealMatrix :=
  fun row column => matrix.val row.castSucc column.castSucc -
    matrix.val row.castSucc 2 * matrix.val 2 column.castSucc / matrix.val 2 2

theorem realPlaneSchurBlock_det (matrix : RealGL3) (pivot : matrix.val 2 2 ≠ 0) :
    (realPlaneSchurBlock matrix).det * matrix.val 2 2 = matrix.val.det := by
  simp only [realPlaneSchurBlock, Matrix.det_fin_two, Matrix.det_fin_three]
  change ((matrix.val 0 0 - matrix.val 0 2 * matrix.val 2 0 / matrix.val 2 2) *
      (matrix.val 1 1 - matrix.val 1 2 * matrix.val 2 1 / matrix.val 2 2) -
    (matrix.val 0 1 - matrix.val 0 2 * matrix.val 2 1 / matrix.val 2 2) *
      (matrix.val 1 0 - matrix.val 1 2 * matrix.val 2 0 / matrix.val 2 2)) * matrix.val 2 2 = _
  field_simp [pivot]
  ring

theorem realPlaneSchurBlock_det_ne_zero (matrix : RealGL3) (pivot : matrix.val 2 2 ≠ 0) :
    (realPlaneSchurBlock matrix).det ≠ 0 := by
  intro zero
  have equality := realPlaneSchurBlock_det matrix pivot
  rw [zero, zero_mul] at equality
  exact (GeneralLinearGroup.det matrix).ne_zero equality.symm

def realPlaneOpenProjection (matrix : RealGL3) : RealPlaneGroup :=
  ⟨Multiplicative.ofAdd (fun row => matrix.val row.castSucc 2 / matrix.val 2 2),
    invertibleMatrix (realPlaneSchurBlock matrix)⟩

theorem realPlaneOpenProjection_matrix (matrix : RealGL3) (pivot : matrix.val 2 2 ≠ 0) :
    (realPlaneMatrix (realPlaneOpenProjection matrix)).val =
      !![matrix.val 0 0 - matrix.val 0 2 * matrix.val 2 0 / matrix.val 2 2,
          matrix.val 0 1 - matrix.val 0 2 * matrix.val 2 1 / matrix.val 2 2,
          matrix.val 0 2 / matrix.val 2 2;
        matrix.val 1 0 - matrix.val 1 2 * matrix.val 2 0 / matrix.val 2 2,
          matrix.val 1 1 - matrix.val 1 2 * matrix.val 2 1 / matrix.val 2 2,
          matrix.val 1 2 / matrix.val 2 2;
        0, 0, 1] := by
  have block := invertibleMatrix_val (realPlaneSchurBlock matrix) (realPlaneSchurBlock_det_ne_zero matrix pivot)
  rw [realPlaneMatrix_apply]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [realPlaneOpenProjection, realPlaneRadicalMatrix, planeUnipotent, planeLevi, planeBlock,
      Matrix.mul_apply, Fin.sum_univ_three, block, realPlaneSchurBlock]

theorem realPlaneOpenProjection_factorization (matrix : RealGL3) (pivot : matrix.val 2 2 ≠ 0) :
    matrix = realPlaneMatrix (realPlaneOpenProjection matrix) *
      planeLevi 1 (Units.mk0 (matrix.val 2 2) pivot) *
        lowerPlaneUnipotent (matrix.val 2 0 / matrix.val 2 2) (matrix.val 2 1 / matrix.val 2 2) := by
  apply Units.ext
  simp only [GeneralLinearGroup.coe_mul, realPlaneOpenProjection_matrix matrix pivot]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, lowerPlaneUnipotent, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp <;> first | ring

theorem realPlaneMatrix_last_row (element : RealPlaneGroup) (column : Fin 3) :
    (realPlaneMatrix element).val 2 column = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 column := by
  rw [realPlaneMatrix_apply]
  fin_cases column <;>
    simp [realPlaneRadicalMatrix, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem realPlaneMatrix_mul_last_row (element : RealPlaneGroup) (matrix : RealGL3) (column : Fin 3) :
    (realPlaneMatrix element * matrix).val 2 column = matrix.val 2 column := by
  simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, realPlaneMatrix_last_row,
    Matrix.one_apply, Fin.sum_univ_three]
  simp

theorem realPlaneOpenProjection_equivariant (element : RealPlaneGroup) (matrix : RealGL3)
    (pivot : matrix.val 2 2 ≠ 0) :
    realPlaneOpenProjection (realPlaneMatrix element * matrix) = element * realPlaneOpenProjection matrix := by
  have product_pivot : (realPlaneMatrix element * matrix).val 2 2 ≠ 0 := by
    rw [realPlaneMatrix_mul_last_row]
    exact pivot
  have factor := realPlaneOpenProjection_factorization (realPlaneMatrix element * matrix) product_pivot
  simp only [realPlaneMatrix_mul_last_row] at factor
  have translated := congrArg (fun value : RealGL3 => realPlaneMatrix element * value)
    (realPlaneOpenProjection_factorization matrix pivot)
  apply realPlaneMatrix_injective
  rw [map_mul]
  apply mul_right_cancel (b := planeLevi (1 : BinaryRealGL) (Units.mk0 (matrix.val 2 2) pivot))
  apply mul_right_cancel (b := lowerPlaneUnipotent (matrix.val 2 0 / matrix.val 2 2)
    (matrix.val 2 1 / matrix.val 2 2))
  simpa only [mul_assoc] using factor.symm.trans translated

theorem realPlaneOpenProjection_retract (element : RealPlaneGroup) :
    realPlaneOpenProjection (realPlaneMatrix element) = element := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext row
    change (realPlaneMatrix element).val row.castSucc 2 / (realPlaneMatrix element).val 2 2 = _
    rw [realPlaneMatrix_radical_entry, realPlaneMatrix_last_row]
    simp
  · change invertibleMatrix (realPlaneSchurBlock (realPlaneMatrix element)) = element.right
    have block : realPlaneSchurBlock (realPlaneMatrix element) = element.right.val := by
      funext row column
      simp only [realPlaneSchurBlock, realPlaneMatrix_binary_entry, realPlaneMatrix_last_row]
      fin_cases column <;> simp
    rw [block, invertibleMatrix_coe]

theorem realPlaneOpenProjection_contDiffAt {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (input : P → RealGL3) (center : P)
    (regular : ContDiffAt ℝ ⊤ (fun point => (input point).val) center)
    (pivot : (input center).val 2 2 ≠ 0) :
    ContDiffAt ℝ ⊤ (fun point => (realPlaneMatrix (realPlaneOpenProjection (input point))).val) center := by
  have entry (row column : Fin 3) : ContDiffAt ℝ ⊤ (fun point => (input point).val row column) center :=
    contDiffAt_pi.mp (contDiffAt_pi.mp regular row) column
  have block (row column : Fin 3) : ContDiffAt ℝ ⊤ (fun point =>
      (input point).val row column - (input point).val row 2 * (input point).val 2 column /
        (input point).val 2 2) center :=
    (entry row column).sub (((entry row 2).mul (entry 2 column)).div (entry 2 2) pivot)
  have quotient (row : Fin 3) : ContDiffAt ℝ ⊤
      (fun point => (input point).val row 2 / (input point).val 2 2) center :=
    (entry row 2).div (entry 2 2) pivot
  let expression (point : P) : Matrix (Fin 3) (Fin 3) ℝ :=
    !![(input point).val 0 0 - (input point).val 0 2 * (input point).val 2 0 / (input point).val 2 2,
        (input point).val 0 1 - (input point).val 0 2 * (input point).val 2 1 / (input point).val 2 2,
        (input point).val 0 2 / (input point).val 2 2;
      (input point).val 1 0 - (input point).val 1 2 * (input point).val 2 0 / (input point).val 2 2,
        (input point).val 1 1 - (input point).val 1 2 * (input point).val 2 1 / (input point).val 2 2,
        (input point).val 1 2 / (input point).val 2 2;
      0, 0, 1]
  have expression_regular : ContDiffAt ℝ ⊤ expression center := by
    apply contDiffAt_pi.mpr
    intro row
    apply contDiffAt_pi.mpr
    intro column
    fin_cases row <;> fin_cases column
    · exact block 0 0
    · exact block 0 1
    · exact quotient 0
    · exact block 1 0
    · exact block 1 1
    · exact quotient 1
    · exact contDiffAt_const
    · exact contDiffAt_const
    · exact contDiffAt_const
  apply expression_regular.congr_of_eventuallyEq
  filter_upwards [(entry 2 2).continuousAt.eventually_ne pivot] with point nonzero
  exact realPlaneOpenProjection_matrix (input point) nonzero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
