module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CasimirNorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCasimir TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirConjugation

noncomputable def adjugateConjugation (matrix direction : BinaryMatrix) : BinaryMatrix :=
  matrix.adjugate * direction * matrix

theorem adjugateConjugation_diagonal (matrix : BinaryMatrix) :
    adjugateConjugation matrix diagonalMatrix =
      (matrix 0 0 * matrix 1 1 + matrix 0 1 * matrix 1 0) • diagonalMatrix +
      (matrix 0 1 * matrix 1 1 - matrix 0 0 * matrix 1 0) • symmetricMatrix -
      (matrix 0 0 * matrix 1 0 + matrix 0 1 * matrix 1 1) • rotationMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [adjugateConjugation, Matrix.adjugate_fin_two, diagonalMatrix, symmetricMatrix,
      rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem adjugateConjugation_symmetric (matrix : BinaryMatrix) :
    adjugateConjugation matrix symmetricMatrix =
      (matrix 1 0 * matrix 1 1 - matrix 0 0 * matrix 0 1) • diagonalMatrix +
      ((matrix 0 0 ^ 2 + matrix 1 1 ^ 2 - matrix 0 1 ^ 2 - matrix 1 0 ^ 2) / 2) • symmetricMatrix +
      ((matrix 0 0 ^ 2 + matrix 0 1 ^ 2 - matrix 1 0 ^ 2 - matrix 1 1 ^ 2) / 2) • rotationMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [adjugateConjugation, Matrix.adjugate_fin_two, diagonalMatrix, symmetricMatrix,
      rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem adjugateConjugation_rotation (matrix : BinaryMatrix) :
    adjugateConjugation matrix rotationMatrix =
      (-(matrix 0 0 * matrix 0 1 + matrix 1 0 * matrix 1 1)) • diagonalMatrix +
      ((matrix 0 0 ^ 2 + matrix 1 0 ^ 2 - matrix 0 1 ^ 2 - matrix 1 1 ^ 2) / 2) • symmetricMatrix +
      ((matrix 0 0 ^ 2 + matrix 0 1 ^ 2 + matrix 1 0 ^ 2 + matrix 1 1 ^ 2) / 2) • rotationMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [adjugateConjugation, Matrix.adjugate_fin_two, diagonalMatrix, symmetricMatrix,
      rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem adjugate_casimir (data : CuspidalRepresentation) (matrix : BinaryMatrix) :
    directionalOperator data (adjugateConjugation matrix diagonalMatrix) ^ 2 +
      directionalOperator data (adjugateConjugation matrix symmetricMatrix) ^ 2 -
      directionalOperator data (adjugateConjugation matrix rotationMatrix) ^ 2 =
      ((matrix.det : ℂ) ^ 2) • casimir data := by
  rw [adjugateConjugation_diagonal, adjugateConjugation_symmetric, adjugateConjugation_rotation]
  simp only [directionalOperator_add, directionalOperator_sub, directionalOperator_real_smul,
    Matrix.det_fin_two, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_neg,
    casimir, rotationOperator, diagonalOperator, symmetricOperator]
  simp only [pow_two, add_mul, sub_mul, mul_add, mul_sub, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul]
  module

theorem conjugation_eq_adjugate (matrix : BinaryRealGL) (direction : BinaryMatrix) :
    conjugation matrix direction = matrix.val.det⁻¹ • adjugateConjugation matrix.val direction := by
  rw [conjugation_apply, Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [smul_mul_assoc, adjugateConjugation]

/-- The quadratic operator is invariant under conjugation by every real binary invertible matrix. -/
theorem conjugate_casimir (data : CuspidalRepresentation) (matrix : BinaryRealGL) :
    directionalOperator data (conjugation matrix diagonalMatrix) ^ 2 +
      directionalOperator data (conjugation matrix symmetricMatrix) ^ 2 -
      directionalOperator data (conjugation matrix rotationMatrix) ^ 2 = casimir data := by
  simp only [conjugation_eq_adjugate, directionalOperator_real_smul, smul_pow, ← smul_add, ← smul_sub]
  rw [adjugate_casimir, smul_smul]
  have cancellation : ((matrix.val.det⁻¹ : ℝ) : ℂ) ^ 2 * (matrix.val.det : ℂ) ^ 2 = 1 := by
    rw [← mul_pow, ← Complex.ofReal_mul, inv_mul_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero matrix)]
    norm_num
  rw [cancellation, one_smul]

theorem directional_square_translate (data : CuspidalRepresentation) (matrix : BinaryRealGL)
    (vector : data.smooth) (direction : BinaryMatrix) :
    (directionalOperator data direction ^ 2) (smoothTranslate data matrix vector) =
      smoothTranslate data matrix ((directionalOperator data (conjugation matrix direction) ^ 2) vector) := by
  simp only [pow_two, Module.End.mul_apply, directionalOperator_translate]

theorem casimir_translate (data : CuspidalRepresentation) (matrix : BinaryRealGL)
    (vector : data.smooth) :
    casimir data (smoothTranslate data matrix vector) = smoothTranslate data matrix (casimir data vector) := by
  have diagonal : (diagonalOperator data ^ 2) (smoothTranslate data matrix vector) =
      smoothTranslate data matrix ((directionalOperator data (conjugation matrix diagonalMatrix) ^ 2) vector) :=
    directional_square_translate data matrix vector diagonalMatrix
  have symmetric : (symmetricOperator data ^ 2) (smoothTranslate data matrix vector) =
      smoothTranslate data matrix ((directionalOperator data (conjugation matrix symmetricMatrix) ^ 2) vector) :=
    directional_square_translate data matrix vector symmetricMatrix
  have rotation : (rotationOperator data ^ 2) (smoothTranslate data matrix vector) =
      smoothTranslate data matrix ((directionalOperator data (conjugation matrix rotationMatrix) ^ 2) vector) :=
    directional_square_translate data matrix vector rotationMatrix
  change (diagonalOperator data ^ 2) (smoothTranslate data matrix vector) +
    (symmetricOperator data ^ 2) (smoothTranslate data matrix vector) -
    (rotationOperator data ^ 2) (smoothTranslate data matrix vector) = _
  rw [diagonal, symmetric, rotation, ← map_add, ← map_sub]
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (conjugate_casimir data matrix)
  exact congrArg (smoothTranslate data matrix) equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirConjugation
