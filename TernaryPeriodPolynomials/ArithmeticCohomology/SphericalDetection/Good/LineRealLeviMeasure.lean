module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRealLevi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineLeviRealMatrix (matrix : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(matrix.val 1 1 : ℝ), (matrix.val 0 1 : ℝ);
    (matrix.val 1 0 : ℝ), (matrix.val 0 0 : ℝ)]

theorem goodLineLeviRealMatrix_det (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (goodLineLeviRealMatrix matrix).det = (matrix.val.det : ℝ) := by
  rw [goodLineLeviRealMatrix, Matrix.det_fin_two]
  change (matrix.val 1 1 : ℝ) * (matrix.val 0 0 : ℝ) -
    (matrix.val 0 1 : ℝ) * (matrix.val 1 0 : ℝ) = (matrix.val.det : ℝ)
  rw [Matrix.det_fin_two]
  push_cast
  ring

theorem goodLineLeviRealMatrix_abs_det (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    |(goodLineLeviRealMatrix matrix).det| = 1 := by
  rw [goodLineLeviRealMatrix_det]
  have integral : |matrix.val.det| = 1 := Int.isUnit_iff_abs_eq.mp (GeneralLinearGroup.det matrix).isUnit
  exact_mod_cast integral

theorem goodLineLeviRealInput_mul (first second : GeneralLinearGroup (Fin 2) ℤ) (real : ℝ × ℝ) :
    goodLineLeviRealInput first (goodLineLeviRealInput second real) =
      goodLineLeviRealInput (second * first) real := by
  ext <;> simp [goodLineLeviRealInput, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem goodLineLeviRealInput_one (real : ℝ × ℝ) :
    goodLineLeviRealInput 1 real = real := by
  ext <;> simp [goodLineLeviRealInput]

def goodLineLeviRealEquiv (matrix : GeneralLinearGroup (Fin 2) ℤ) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun := goodLineLeviRealInput matrix
  invFun := goodLineLeviRealInput matrix⁻¹
  left_inv real := by rw [goodLineLeviRealInput_mul, mul_inv_cancel, goodLineLeviRealInput_one]
  right_inv real := by rw [goodLineLeviRealInput_mul, inv_mul_cancel, goodLineLeviRealInput_one]
  map_add' first second := by ext <;> simp [goodLineLeviRealInput] <;> ring
  map_smul' scalar real := by ext <;> simp [goodLineLeviRealInput] <;> ring

theorem goodLineLeviRealInput_measurePreserving (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    MeasurePreserving (goodLineLeviRealInput matrix) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
  have absolute := goodLineLeviRealMatrix_abs_det matrix
  have nonzero : (goodLineLeviRealMatrix matrix).det ≠ 0 := by
    intro zero
    rw [zero, abs_zero] at absolute
    exact zero_ne_one absolute
  have linear_preserving : MeasurePreserving (Matrix.toLin' (goodLineLeviRealMatrix matrix))
      (volume : Measure (Fin 2 → ℝ)) volume := by
    refine ⟨(Matrix.toLin' (goodLineLeviRealMatrix matrix)).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi nonzero, abs_inv, absolute, inv_one,
      ENNReal.ofReal_one, one_smul]
  have to_pair := measurePreserving_finTwoArrow (volume : Measure ℝ)
  have to_vector := to_pair.symm MeasurableEquiv.finTwoArrow
  have composed := to_pair.comp (linear_preserving.comp to_vector)
  convert composed using 1
  funext real
  ext <;> simp [goodLineLeviRealInput, goodLineLeviRealMatrix, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem integral_goodLineLeviRealInput {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℝ × ℝ → E) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (∫ real : ℝ × ℝ, function (goodLineLeviRealInput matrix real)
      ∂((volume : Measure ℝ).prod volume)) =
    ∫ real : ℝ × ℝ, function real ∂((volume : Measure ℝ).prod volume) :=
  (goodLineLeviRealInput_measurePreserving matrix).integral_comp
    (goodLineLeviRealEquiv matrix).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding function

end TernaryPeriodPolynomials.SphericalDetection.Helpers
