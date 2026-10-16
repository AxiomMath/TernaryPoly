module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ParabolicFactorization
public import Mathlib.Tactic
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Valuation.IsTrivialOn

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem valuation_pair_integral_elimination {K : Type*} [Field K]
    (integers : ValuationSubring K) (first second : K) :
    ∃ matrix : GeneralLinearGroup (Fin 2) integers,
      first * (matrix.val 0 0 : K) + second * (matrix.val 1 0 : K) = 0 := by
  by_cases second_zero : second = 0
  · let matrix : GeneralLinearGroup (Fin 2) integers :=
      ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
        ext row column
        fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
        ext row column
        fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    exact ⟨matrix, by simp [matrix, second_zero]⟩
  · by_cases quotient_integral : first / second ∈ integers
    · let quotient : integers := ⟨first / second, quotient_integral⟩
      let matrix : GeneralLinearGroup (Fin 2) integers :=
        ⟨!![1, 0; -quotient, 1], !![1, 0; quotient, 1], by
          ext row column
          fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
          ext row column
          fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
      refine ⟨matrix, ?_⟩
      simp [matrix, quotient]
      field_simp
      ring
    · have reverse_integral : second / first ∈ integers := by
        simpa only [inv_div] using (integers.mem_or_inv_mem (first / second)).resolve_left quotient_integral
      have first_nonzero : first ≠ 0 := by
        intro first_zero
        apply quotient_integral
        simp [first_zero]
      let quotient : integers := ⟨second / first, reverse_integral⟩
      let matrix : GeneralLinearGroup (Fin 2) integers :=
        ⟨!![-quotient, 1; 1, 0], !![0, 1; 1, quotient], by
          ext row column
          fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
          ext row column
          fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
      refine ⟨matrix, ?_⟩
      simp [matrix, quotient]
      field_simp
      ring

theorem valuation_first_integral_elimination {K : Type*} [Field K]
    (integers : ValuationSubring K) (matrix : GL3 K) :
    ∃ integralMatrix : GL3 integers,
      (matrix * GeneralLinearGroup.map integers.subtype integralMatrix).val 2 0 = 0 := by
  obtain ⟨binary, elimination⟩ := valuation_pair_integral_elimination integers (matrix.val 2 0) (matrix.val 2 1)
  refine ⟨planeLevi binary 1, ?_⟩
  change (matrix.val * (GeneralLinearGroup.map integers.subtype (planeLevi binary 1)).val) 2 0 = 0
  simpa [GeneralLinearGroup.map_apply, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
    using elimination

theorem valuation_integral_plane_elimination {K : Type*} [Field K]
    (integers : ValuationSubring K) (matrix : GL3 K) :
    ∃ integralMatrix : GL3 integers,
      InPlaneParabolic (matrix * GeneralLinearGroup.map integers.subtype integralMatrix) := by
  obtain ⟨first, first_zero⟩ := valuation_first_integral_elimination integers matrix
  let intermediate := matrix * GeneralLinearGroup.map integers.subtype first
  obtain ⟨binary, elimination⟩ :=
    valuation_pair_integral_elimination integers (intermediate.val 2 1) (intermediate.val 2 2)
  refine ⟨first * lineLevi 1 binary, ?_⟩
  rw [map_mul, ← mul_assoc]
  constructor
  · change (intermediate.val * (GeneralLinearGroup.map integers.subtype (lineLevi 1 binary)).val) 2 0 = 0
    simpa [GeneralLinearGroup.map_apply, lineLevi_val, Matrix.mul_apply, Fin.sum_univ_three] using
      (show intermediate.val 2 0 = 0 from first_zero)
  · change (intermediate.val * (GeneralLinearGroup.map integers.subtype (lineLevi 1 binary)).val) 2 1 = 0
    simpa [GeneralLinearGroup.map_apply, lineLevi_val, Matrix.mul_apply, Fin.sum_univ_three] using elimination

noncomputable def integralMatrixOfLocals
    (matrices : ∀ place : FinitePlace, GL3 (place.adicCompletionIntegers ℚ)) : GL3 IntegralAdeles :=
  Units.map Matrix.piRingEquiv.symm.toMonoidHom
    ⟨fun place => (matrices place).val, fun place => (matrices place).inv,
      funext (fun place => (matrices place).val_inv), funext (fun place => (matrices place).inv_val)⟩

theorem integralMatrixOfLocals_evaluation
    (matrices : ∀ place : FinitePlace, GL3 (place.adicCompletionIntegers ℚ)) (place : FinitePlace) :
    finiteGLAt place (GeneralLinearGroup.map integralEmbedding (integralMatrixOfLocals matrices)) =
      GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype (matrices place) := by
  apply Units.ext
  rfl

theorem finite_integral_plane_elimination (matrix : FiniteGL) :
    ∃ integralMatrix : GL3 IntegralAdeles,
      InPlaneParabolic (matrix * GeneralLinearGroup.map integralEmbedding integralMatrix) := by
  classical
  choose localMatrices local_parabolic using (fun place : FinitePlace =>
    valuation_integral_plane_elimination (place.adicCompletionIntegers ℚ) (finiteGLAt place matrix))
  refine ⟨integralMatrixOfLocals localMatrices, ?_⟩
  have local_spec (place : FinitePlace) :
      InPlaneParabolic (finiteGLAt place
        (matrix * GeneralLinearGroup.map integralEmbedding (integralMatrixOfLocals localMatrices))) := by
    rw [map_mul, integralMatrixOfLocals_evaluation]
    exact local_parabolic place
  constructor
  · apply Subtype.ext
    funext place
    exact (local_spec place).1
  · apply Subtype.ext
    funext place
    exact (local_spec place).2

theorem finite_plane_decomposition (matrix : FiniteGL) :
    ∃ (parabolic : FiniteGL) (integralMatrix : GL3 IntegralAdeles),
      matrix = parabolic * GeneralLinearGroup.map integralEmbedding integralMatrix ∧
      InPlaneParabolic parabolic := by
  obtain ⟨integralMatrix, parabolic⟩ := finite_integral_plane_elimination matrix
  exact ⟨matrix * GeneralLinearGroup.map integralEmbedding integralMatrix, integralMatrix⁻¹, by simp, parabolic⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
