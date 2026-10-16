module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IntegralLatticeBasis

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteMatrix_mulVec_integral {row column : Type*} [Fintype column]
    (matrix : Matrix row column FiniteAdeles) (vector : column → FiniteAdeles)
    (matrix_integral : ∀ i j, matrix i j ∈ Set.range integralEmbedding)
    (vector_integral : ∀ j, vector j ∈ Set.range integralEmbedding) :
    ∀ i, matrix.mulVec vector i ∈ Set.range integralEmbedding := by
  intro i
  exact integralEmbedding.range.sum_mem (fun j _ =>
    integralEmbedding.range.mul_mem (matrix_integral i j) (vector_integral j))

theorem finiteMatrix_mulVec_scaled_integral {row column : Type*} [Fintype column]
    (matrix : Matrix row column FiniteAdeles) (vector : column → FiniteAdeles) (scalar : FiniteAdeles)
    (matrix_integral : ∀ i j, matrix i j * scalar ∈ Set.range integralEmbedding)
    (vector_integral : ∀ j, vector j ∈ Set.range integralEmbedding) :
    ∀ i, matrix.mulVec (scalar • vector) i ∈ Set.range integralEmbedding := by
  intro i
  have equality : matrix.mulVec (scalar • vector) i =
      Matrix.mulVec (fun i j => matrix i j * scalar) vector i := by
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [equality]
  exact finiteMatrix_mulVec_integral _ vector matrix_integral vector_integral i

def finiteIntegralPreimageLattice {dimension : ℕ}
    (matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles) : Submodule ℤ (Fin dimension → ℤ) where
  carrier := {vector | ∀ row, matrix⁻¹.val.mulVec (fun column => (vector column : FiniteAdeles)) row ∈
    Set.range integralEmbedding}
  zero_mem' := by
    intro row
    change matrix⁻¹.val.mulVec (0 : Fin dimension → FiniteAdeles) row ∈ _
    rw [Matrix.mulVec_zero, Pi.zero_apply]
    exact ⟨0, map_zero _⟩
  add_mem' := by
    intro a b first second row
    simp only [Pi.add_apply, Int.cast_add]
    change matrix⁻¹.val.mulVec ((fun column => (a column : FiniteAdeles)) +
      (fun column => (b column : FiniteAdeles))) row ∈ _
    rw [Matrix.mulVec_add, Pi.add_apply]
    exact integralEmbedding.range.add_mem (first row) (second row)
  smul_mem' scalar vector integral := by
    intro row
    have equality : (fun column => ((scalar • vector) column : FiniteAdeles)) =
        (scalar : FiniteAdeles) • (fun column => (vector column : FiniteAdeles)) := by
      funext column
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [equality, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact integralEmbedding.range.mul_mem ⟨(scalar : IntegralAdeles), map_intCast _ scalar⟩ (integral row)

theorem finiteIntegralPreimageLattice_contains_multiple {dimension : ℕ}
    (matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles) :
    ∃ denominator : ℕ, 0 < denominator ∧ ∀ vector : Fin dimension → ℤ,
      (denominator : ℤ) • vector ∈ finiteIntegralPreimageLattice matrix := by
  obtain ⟨denominator, positive, integral⟩ := finiteAdeles_exists_common_denominator
    (fun position : Fin dimension × Fin dimension => matrix⁻¹.val position.1 position.2)
  refine ⟨denominator, positive, fun vector row => ?_⟩
  have equality : (fun column => (((denominator : ℤ) • vector) column : FiniteAdeles)) =
      (denominator : FiniteAdeles) • (fun column => (vector column : FiniteAdeles)) := by
    funext column
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  rw [equality]
  exact finiteMatrix_mulVec_scaled_integral matrix⁻¹.val _ _
    (fun row column => integral (row, column))
    (fun column => ⟨(vector column : IntegralAdeles), map_intCast _ _⟩) row

theorem finiteIntegralPreimageLattice_exists_basis {dimension : ℕ}
    (matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles) :
    ∃ basis : Matrix (Fin dimension) (Fin dimension) ℤ, basis.det ≠ 0 ∧
      ∀ vector, vector ∈ finiteIntegralPreimageLattice matrix ↔
        ∃ coordinates : Fin dimension → ℤ, basis.mulVec coordinates = vector := by
  obtain ⟨denominator, positive, contains⟩ := finiteIntegralPreimageLattice_contains_multiple matrix
  exact integer_lattice_exists_basis_matrix _ (denominator : ℤ)
    (Nat.cast_ne_zero.mpr (ne_of_gt positive)) contains

theorem integralFiniteVector_approximate {index : Type*} (vector : index → FiniteAdeles)
    (integral : ∀ position, vector position ∈ Set.range integralEmbedding)
    (denominator : ℕ) (positive : 0 < denominator) :
    ∃ (integer : index → ℤ) (remainder : index → IntegralAdeles),
      vector = (fun position => (integer position : FiniteAdeles)) +
        (denominator : FiniteAdeles) • (fun position => integralEmbedding (remainder position)) := by
  choose values values_eq using integral
  choose integer remainder remainder_eq using fun position =>
    integralAdeles_exists_integer_residue denominator positive (values position)
  refine ⟨integer, remainder, ?_⟩
  funext position
  have mapped := congrArg integralEmbedding (remainder_eq position)
  simp only [map_sub, map_mul, map_intCast, map_natCast, values_eq] at mapped
  change vector position = (integer position : FiniteAdeles) +
    (denominator : FiniteAdeles) * integralEmbedding (remainder position)
  linear_combination mapped

end TernaryPeriodPolynomials.SphericalDetection.Helpers
