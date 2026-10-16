module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.FiniteTriangular
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.IdeleDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.Periodicity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_triangular_rational_integral (matrix : BinaryFiniteGL)
    (triangular : matrix.val 1 0 = 0) :
    ∃ rational : GeneralLinearGroup (Fin 2) ℚ,
      ∃ integralMatrix : GeneralLinearGroup (Fin 2) IntegralAdeles,
        matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
          GeneralLinearGroup.map integralEmbedding integralMatrix := by
  obtain ⟨first_unit, second_unit⟩ := binary_triangular_diagonal_units matrix triangular
  obtain ⟨first, first_value⟩ := first_unit
  obtain ⟨second, second_value⟩ := second_unit
  obtain ⟨firstRational, _, firstIntegral, first_decomposition⟩ :=
    finiteIdele_rational_integral_decomposition first
  obtain ⟨secondRational, _, secondIntegral, second_decomposition⟩ :=
    finiteIdele_rational_integral_decomposition second
  let rationalMap := algebraMap ℚ FiniteAdeles
  let firstFinite := Units.map rationalMap.toMonoidHom firstRational
  let secondFinite := Units.map integralEmbedding.toMonoidHom secondIntegral
  let coordinate := matrix.val 0 1 * (firstFinite⁻¹).val * (secondFinite⁻¹).val
  obtain ⟨rationalCoordinate, integralCoordinate, approximation⟩ :=
    finiteAdele_rational_approximation coordinate
  have entry_identity : matrix.val 0 1 =
      firstFinite.val * (integralEmbedding integralCoordinate + rationalMap rationalCoordinate) *
        secondFinite.val := by
    calc
      _ = firstFinite.val * coordinate * secondFinite.val := by
        dsimp only [coordinate]
        simp [mul_assoc, mul_left_comm, mul_comm]
      _ = _ := by rw [sub_eq_iff_eq_add.mp approximation]
  have first_entry : matrix.val 0 0 =
      rationalMap firstRational.val * integralEmbedding firstIntegral.val := by
    rw [← first_value, first_decomposition]
    rfl
  have second_entry : matrix.val 1 1 =
      rationalMap secondRational.val * integralEmbedding secondIntegral.val := by
    rw [← second_value, second_decomposition]
    rfl
  refine ⟨binaryUnitDiagonal firstRational secondRational * binaryUnipotent rationalCoordinate,
    binaryUnipotent integralCoordinate * binaryUnitDiagonal firstIntegral secondIntegral, ?_⟩
  rw [map_mul, map_mul, map_binaryUnitDiagonal, map_binaryUnitDiagonal,
    map_binaryUnipotent, map_binaryUnipotent]
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUnitDiagonal, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  · exact first_entry
  · rw [entry_identity]
    simp only [Algebra.smul_def]
    change (algebraMap ℚ FiniteAdeles) firstRational.val *
      (integralEmbedding integralCoordinate + (algebraMap ℚ FiniteAdeles) rationalCoordinate) *
        integralEmbedding secondIntegral.val = _
    ring
  · exact triangular
  · exact second_entry

theorem binary_finite_rational_integral_decomposition (matrix : BinaryFiniteGL) :
    ∃ rational : GeneralLinearGroup (Fin 2) ℚ,
      ∃ integralMatrix : GeneralLinearGroup (Fin 2) IntegralAdeles,
        matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
          GeneralLinearGroup.map integralEmbedding integralMatrix := by
  obtain ⟨eliminator, triangular⟩ := binary_finite_integral_triangular matrix
  obtain ⟨rational, integralMatrix, decomposition⟩ :=
    binary_triangular_rational_integral _ triangular
  refine ⟨rational, integralMatrix * eliminator⁻¹, ?_⟩
  rw [map_mul, ← mul_assoc, ← decomposition]
  simp

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
