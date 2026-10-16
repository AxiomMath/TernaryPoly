module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealRowBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.IntegralIdeleBound

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FiniteMatrixBounds

theorem common_denominator (matrix : Matrix (Fin 3) (Fin 3) FiniteAdeles) :
    ∃ number : ℕ, number ≠ 0 ∧ ∃ integral : Matrix (Fin 3) (Fin 3) IntegralAdeles,
      integral.map integralEmbedding = (number : FiniteAdeles) • matrix := by
  have clears : ∀ index : Fin 3 × Fin 3, ∃ number : ℕ, number ≠ 0 ∧
      ∃ integral : IntegralAdeles, integralEmbedding integral = matrix index.1 index.2 * number := by
    intro index
    exact FiniteApproximation.common_natural_denominator _
  choose denominators nonzero integrals equality using clears
  let number := ∏ index : Fin 3 × Fin 3, denominators index
  have factors : ∀ index : Fin 3 × Fin 3, ∃ factor : ℕ, number = denominators index * factor := by
    intro index
    exact Finset.dvd_prod_of_mem denominators (Finset.mem_univ index)
  choose factors factorization using factors
  refine ⟨number, Finset.prod_ne_zero_iff.mpr (fun index _ => nonzero index),
    fun row column => integrals (row, column) * (factors (row, column) : IntegralAdeles), ?_⟩
  apply Matrix.ext
  intro row column
  change integralEmbedding (integrals (row, column) * (factors (row, column) : IntegralAdeles)) =
    (number : FiniteAdeles) * matrix row column
  rw [map_mul, map_natCast, equality, factorization (row, column), Nat.cast_mul]
  ring

theorem primitive_scalar_integral (row : Fin 3 → ℤ)
    (primitive : ∃ coefficients : Fin 3 → ℤ, ∑ index, row index * coefficients index = 1)
    (scalar : FiniteAdeles)
    (integral : ∀ index, scalar * (row index : FiniteAdeles) ∈ Set.range integralEmbedding) :
    scalar ∈ Set.range integralEmbedding := by
  obtain ⟨coefficients, equality⟩ := primitive
  have castEquality : (∑ index, (row index : FiniteAdeles) * (coefficients index : FiniteAdeles)) = 1 := by
    simpa only [map_sum, map_mul, map_one, Int.coe_castRingHom] using
      congrArg (Int.castRingHom FiniteAdeles) equality
  have sumIntegral : (∑ index, (scalar * (row index : FiniteAdeles)) * (coefficients index : FiniteAdeles)) ∈
      integralEmbedding.range := by
    apply Subring.sum_mem
    intro index _
    exact integralEmbedding.range.mul_mem (integral index) ⟨coefficients index, map_intCast _ _⟩
  change scalar ∈ integralEmbedding.range
  simpa only [mul_assoc, ← Finset.mul_sum, castEquality, mul_one] using sumIntegral

theorem primitive_row_denominator (row : Fin 3 → ℤ)
    (primitive : ∃ coefficients : Fin 3 → ℤ, ∑ index, row index * coefficients index = 1)
    (argument : FiniteGL) (number : ℕ) (integralInverse : Matrix (Fin 3) (Fin 3) IntegralAdeles)
    (inverseEquality : integralInverse.map integralEmbedding = (number : FiniteAdeles) • argument.inv)
    (unit : FiniteAdelesˣ) (compact : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (rowEquality : (fun index => (row index : FiniteAdeles)) ᵥ* argument.val =
      unit.val • (GeneralLinearGroup.map integralEmbedding compact).val 2) :
    (number : FiniteAdeles) * unit.inv ∈ Set.range integralEmbedding := by
  apply primitive_scalar_integral row primitive
  intro index
  refine ⟨(compact.val * integralInverse) 2 index, ?_⟩
  have recovered := congrArg (fun row : Fin 3 → FiniteAdeles => row ᵥ* argument.inv) rowEquality
  rw [Matrix.vecMul_vecMul, argument.val_inv, Matrix.vecMul_one, Matrix.smul_vecMul] at recovered
  have scaled := congrArg (fun row : Fin 3 → FiniteAdeles =>
    ((number : FiniteAdeles) * unit.inv) • row) recovered
  rw [smul_smul, mul_assoc, unit.inv_val, mul_one] at scaled
  have coordinate := congrFun scaled index
  have mapped := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) FiniteAdeles => matrix 2 index)
    (show (compact.val * integralInverse).map integralEmbedding =
      (number : FiniteAdeles) • (compact.val.map integralEmbedding * argument.inv) by
        rw [Matrix.map_mul, inverseEquality, Matrix.mul_smul])
  exact mapped.trans coordinate.symm

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FiniteMatrixBounds
