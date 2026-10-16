module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.IntegralLattice

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteGL_inverse_mulVec_column {dimension : ℕ}
    (matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles) (column : Fin dimension) :
    matrix⁻¹.val.mulVec (fun row => matrix.val row column) = Pi.single column 1 := by
  funext row
  change (matrix⁻¹.val * matrix.val) row column = _
  rw [matrix.inv_mul]
  simp only [Matrix.one_apply, Pi.single_apply]

/-- An integral finite-adelic lattice is the adelic extension of its full integer lattice. -/
theorem finiteGL_integral_factorization {dimension : ℕ}
    (matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles)
    (integral : ∀ row column, matrix.val row column ∈ Set.range integralEmbedding) :
    ∃ (rational : GeneralLinearGroup (Fin dimension) ℚ)
      (compact : GeneralLinearGroup (Fin dimension) IntegralAdeles),
      matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
        GeneralLinearGroup.map integralEmbedding compact := by
  obtain ⟨basis, basis_nonzero, basis_span⟩ := finiteIntegralPreimageLattice_exists_basis matrix
  let rational : GeneralLinearGroup (Fin dimension) ℚ := GeneralLinearGroup.mkOfDetNeZero
    ((Int.castRingHom ℚ).mapMatrix basis) (by
      rw [← RingHom.map_det]
      exact Int.cast_ne_zero.mpr basis_nonzero)
  let mapped := GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational
  have mapped_entries (row column : Fin dimension) : mapped.val row column = (basis row column : FiniteAdeles) := by
    simp [mapped, rational, GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply]
  have inverse_integral (row column : Fin dimension) :
      (matrix⁻¹.val * mapped.val) row column ∈ Set.range integralEmbedding := by
    have basis_member : (fun row => basis row column) ∈ finiteIntegralPreimageLattice matrix :=
      (basis_span _).mpr ⟨Pi.single column 1, Matrix.mulVec_single_one basis column⟩
    change matrix⁻¹.val.mulVec (fun position => mapped.val position column) row ∈ _
    simp only [mapped_entries]
    exact basis_member row
  obtain ⟨denominator, positive, cleared⟩ := finiteAdeles_exists_common_denominator
    (fun position : Bool × Fin dimension × Fin dimension =>
      if position.1 then matrix⁻¹.val position.2.1 position.2.2 else mapped⁻¹.val position.2.1 position.2.2)
  have matrix_cleared (row column : Fin dimension) :
      matrix⁻¹.val row column * (denominator : FiniteAdeles) ∈ Set.range integralEmbedding := by
    simpa only [Bool.true_eq_false, Bool.true_eq, ite_true] using cleared (true, row, column)
  have mapped_cleared (row column : Fin dimension) :
      mapped⁻¹.val row column * (denominator : FiniteAdeles) ∈ Set.range integralEmbedding := by
    simpa only [Bool.false_eq_true, ite_false] using cleared (false, row, column)
  have forward_integral (row column : Fin dimension) :
      (mapped⁻¹.val * matrix.val) row column ∈ Set.range integralEmbedding := by
    obtain ⟨integer, remainder, approximate⟩ := integralFiniteVector_approximate
      (fun position => matrix.val position column) (fun position => integral position column) denominator positive
    let error : Fin dimension → FiniteAdeles :=
      (denominator : FiniteAdeles) • (fun position => integralEmbedding (remainder position))
    have error_integral (operator : Matrix (Fin dimension) (Fin dimension) FiniteAdeles)
        (operator_cleared : ∀ i j, operator i j * (denominator : FiniteAdeles) ∈ Set.range integralEmbedding) :
        ∀ i, operator.mulVec error i ∈ Set.range integralEmbedding :=
      finiteMatrix_mulVec_scaled_integral operator _ _ operator_cleared (fun position => ⟨remainder position, rfl⟩)
    have integer_member : integer ∈ finiteIntegralPreimageLattice matrix := by
      intro position
      have identity := congrArg (fun vector => matrix⁻¹.val.mulVec vector) approximate
      rw [finiteGL_inverse_mulVec_column, Matrix.mulVec_add] at identity
      have component := congrFun identity position
      have equality : matrix⁻¹.val.mulVec (fun position => (integer position : FiniteAdeles)) position =
          (Pi.single column 1 : Fin dimension → FiniteAdeles) position - matrix⁻¹.val.mulVec error position := by
        change (Pi.single column 1 : Fin dimension → FiniteAdeles) position =
          matrix⁻¹.val.mulVec (fun position => (integer position : FiniteAdeles)) position +
            matrix⁻¹.val.mulVec error position at component
        exact eq_sub_of_add_eq component.symm
      rw [equality]
      apply integralEmbedding.range.sub_mem
      · simp only [Pi.single_apply]
        split_ifs <;> first | exact integralEmbedding.range.one_mem | exact integralEmbedding.range.zero_mem
      · exact error_integral _ matrix_cleared position
    obtain ⟨coordinates, coordinates_eq⟩ := (basis_span integer).mp integer_member
    have mapped_coordinates : mapped.val.mulVec (fun position => (coordinates position : FiniteAdeles)) =
        (fun position => (integer position : FiniteAdeles)) := by
      funext position
      have equality := congrArg (fun value : ℤ => (value : FiniteAdeles)) (congrFun coordinates_eq position)
      simpa only [Matrix.mulVec, dotProduct, mapped_entries, Int.cast_sum, Int.cast_mul] using equality
    have mapped_integer : mapped⁻¹.val.mulVec (fun position => (integer position : FiniteAdeles)) =
        (fun position => (coordinates position : FiniteAdeles)) := by
      rw [← mapped_coordinates, Matrix.mulVec_mulVec, mapped.inv_mul, Matrix.one_mulVec]
    change mapped⁻¹.val.mulVec (fun position => matrix.val position column) row ∈ _
    rw [approximate, Matrix.mulVec_add, Pi.add_apply, mapped_integer]
    exact integralEmbedding.range.add_mem ⟨(coordinates row : IntegralAdeles), map_intCast _ _⟩
      (error_integral _ mapped_cleared row)
  have compact_member : mapped⁻¹ * matrix ∈ finiteIntegralGLLevel dimension := by
    apply (finiteIntegralGLLevel_mem_iff _).mpr
    constructor
    · exact forward_integral
    · intro row column
      rw [_root_.mul_inv_rev, inv_inv]
      exact inverse_integral row column
  obtain ⟨compact, compact_eq⟩ := compact_member
  refine ⟨rational, compact, ?_⟩
  change matrix = mapped * GeneralLinearGroup.map integralEmbedding compact
  rw [compact_eq, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Every finite rational adelic matrix is rational times an integral invertible matrix. -/
theorem finiteGL_rational_integral_factorization {dimension : ℕ}
    (matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles) :
    ∃ (rational : GeneralLinearGroup (Fin dimension) ℚ)
      (compact : GeneralLinearGroup (Fin dimension) IntegralAdeles),
      matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
        GeneralLinearGroup.map integralEmbedding compact := by
  obtain ⟨denominator, positive, cleared⟩ := finiteAdeles_exists_common_denominator
    (fun position : Fin dimension × Fin dimension => matrix.val position.1 position.2)
  let scalar := GeneralLinearGroup.scalar (Fin dimension)
    (Units.mk0 (denominator : ℚ) (Nat.cast_ne_zero.mpr (ne_of_gt positive)))
  let mapped := GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) scalar
  have mapped_val : mapped.val = (denominator : FiniteAdeles) • (1 : Matrix (Fin dimension) (Fin dimension) FiniteAdeles) := by
    funext row column
    simp only [mapped, scalar, GeneralLinearGroup.map_apply, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply, Units.val_mk0, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> simp
  have scaled_integral : ∀ row column, (mapped * matrix).val row column ∈ Set.range integralEmbedding := by
    intro row column
    rw [GeneralLinearGroup.coe_mul, mapped_val, Matrix.smul_mul, one_mul, Matrix.smul_apply, smul_eq_mul, mul_comm]
    exact cleared (row, column)
  obtain ⟨rational, compact, factorization⟩ := finiteGL_integral_factorization (mapped * matrix) scaled_integral
  refine ⟨scalar⁻¹ * rational, compact, ?_⟩
  rw [map_mul, map_inv, mul_assoc]
  change matrix = mapped⁻¹ * (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
    GeneralLinearGroup.map integralEmbedding compact)
  rw [← factorization, ← mul_assoc, inv_mul_cancel, one_mul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
