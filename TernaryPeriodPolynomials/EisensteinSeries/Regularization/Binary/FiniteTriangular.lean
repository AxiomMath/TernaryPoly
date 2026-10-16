module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.PlaneDecomposition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def binaryUnitDiagonal {R : Type*} [CommRing R] (first second : Rˣ) :
    GeneralLinearGroup (Fin 2) R :=
  ⟨!![first.val, 0; 0, second.val], !![(first⁻¹).val, 0; 0, (second⁻¹).val], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem map_binaryUnitDiagonal {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (first second : Rˣ) :
    GeneralLinearGroup.map ringMap (binaryUnitDiagonal first second) =
      binaryUnitDiagonal (Units.map ringMap first) (Units.map ringMap second) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map_apply, binaryUnitDiagonal]

noncomputable def binaryIntegralMatrixOfLocals
    (matrices : ∀ place : FinitePlace, GeneralLinearGroup (Fin 2) (place.adicCompletionIntegers ℚ)) :
    GeneralLinearGroup (Fin 2) IntegralAdeles :=
  Units.map Matrix.piRingEquiv.symm.toMonoidHom
    ⟨fun place => (matrices place).val, fun place => (matrices place).inv,
      funext (fun place => (matrices place).val_inv), funext (fun place => (matrices place).inv_val)⟩

theorem binary_finite_integral_triangular (matrix : BinaryFiniteGL) :
    ∃ integralMatrix : GeneralLinearGroup (Fin 2) IntegralAdeles,
      (matrix * GeneralLinearGroup.map integralEmbedding integralMatrix).val 1 0 = 0 := by
  classical
  choose localMatrices local_elimination using (fun place : FinitePlace =>
    valuation_pair_integral_elimination (place.adicCompletionIntegers ℚ)
      (matrix.val 1 0 place) (matrix.val 1 1 place))
  refine ⟨binaryIntegralMatrixOfLocals localMatrices, ?_⟩
  apply Subtype.ext
  funext place
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  exact local_elimination place

theorem binary_triangular_diagonal_units {R : Type*} [CommRing R]
    (matrix : GeneralLinearGroup (Fin 2) R) (triangular : matrix.val 1 0 = 0) :
    IsUnit (matrix.val 0 0) ∧ IsUnit (matrix.val 1 1) := by
  have determinant_unit := (GeneralLinearGroup.det matrix).isUnit
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, triangular, mul_zero, sub_zero]
    at determinant_unit
  exact (Commute.all _ _).isUnit_mul_iff.mp determinant_unit

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
