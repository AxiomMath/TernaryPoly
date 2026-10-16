module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MonomialWeights

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialCoordinates TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialWeights
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialLadder TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TriangularPrimitive

noncomputable def sequence (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) : ℕ → data.smooth
  | 0 => 0
  | position + 1 => (2 * (position + 1 : ℂ))⁻¹ •
      (LieOperators.raising data (sequence data degree vectors position) - component data degree position vectors)

theorem sequence_zero (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    sequence data degree vectors 0 = 0 := rfl

theorem sequence_succ (data : CuspidalRepresentation) (degree position : ℕ) (vectors : Vectors data degree) :
    sequence data degree vectors (position + 1) = (2 * (position + 1 : ℂ))⁻¹ •
      (LieOperators.raising data (sequence data degree vectors position) - component data degree position vectors) := rfl

theorem sequence_eigen (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (eigen : CoefficientRotation.shifted data degree 2 vectors = 0) (position : ℕ) (bound : position ≤ degree + 1) :
    rotationOperator data (sequence data degree vectors position) =
      (Complex.I * weight degree 0 position) • sequence data degree vectors position := by
  induction position with
  | zero => simp only [sequence_zero, map_zero, smul_zero]
  | succ position inductionHypothesis =>
      have previousBound : position ≤ degree + 1 := by omega
      have previousEigen := inductionHypothesis previousBound
      have raisedEigen := LieOperators.raising_eigen data (sequence data degree vectors position)
        (weight degree 0 position) previousEigen
      have vectorEigen := component_eigen data degree position 2 previousBound vectors eigen
      have nextWeight : weight degree 0 position + 2 = weight degree 0 (position + 1) := (weight_succ degree position bound).symm
      have sourceWeight : weight degree 2 position = weight degree 0 (position + 1) :=
        (weight_target degree position 2).trans nextWeight
      rw [sequence_succ, map_smul, map_sub, raisedEigen, vectorEigen, nextWeight, sourceWeight]
      simp only [smul_sub, smul_smul]
      module

theorem sequence_fixed (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (level : Subgroup BinaryFiniteGL) (fixed : ∀ index, (vectors index).val ∈ fixedSubspace data level)
    (position : ℕ) : (sequence data degree vectors position).val ∈ fixedSubspace data level := by
  induction position with
  | zero => exact (fixedSubspace data level).zero_mem
  | succ position inductionHypothesis =>
      exact (fixedSubspace data level).smul_mem _
        ((fixedSubspace data level).sub_mem (raising_preserves_fixed data level _ inductionHypothesis)
          (component_fixed data degree position vectors level fixed))

noncomputable def primitive (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) : Vectors data degree :=
  assemble data degree (sequence data degree vectors)

theorem primitive_eigen (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (eigen : CoefficientRotation.shifted data degree 2 vectors = 0) :
    CoefficientInfinitesimal.operator data degree rotationMatrix (primitive data degree vectors) = 0 := by
  have equality := assemble_eigen data degree 0 (sequence data degree vectors) (sequence_eigen data degree vectors eigen)
  simpa only [primitive, CoefficientRotation.shifted, Int.cast_zero, mul_zero, zero_smul, sub_zero] using equality

theorem primitive_fixed (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (level : Subgroup BinaryFiniteGL) (fixed : ∀ index, (vectors index).val ∈ fixedSubspace data level)
    (index : Index (degree + 1)) : (primitive data degree vectors index).val ∈ fixedSubspace data level :=
  assemble_fixed data degree (sequence data degree vectors) level (fun position _ => sequence_fixed data degree vectors level fixed position) index

theorem primitive_cancels (data : CuspidalRepresentation) (degree position : ℕ) (bound : position < degree + 1)
    (vectors : Vectors data degree) :
    component data degree position (CoefficientLadder.raising data degree (primitive data degree vectors)) =
      component data degree position vectors := by
  rw [component_raising data degree position (by omega)]
  change LieOperators.raising data (component data degree position (assemble data degree (sequence data degree vectors))) -
    (2 * (position + 1 : ℂ)) • component data degree (position + 1) (assemble data degree (sequence data degree vectors)) = _
  rw [component_assemble data degree position (by omega), component_assemble data degree (position + 1) (by omega), sequence_succ]
  have nonzero : (2 * (position + 1 : ℂ)) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact_mod_cast (show position + 1 ≠ 0 by omega)
  rw [smul_smul, mul_inv_cancel₀ nonzero, one_smul]
  abel

noncomputable def residual (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) : Vectors data degree :=
  vectors - CoefficientLadder.raising data degree (primitive data degree vectors)

theorem residual_component_zero (data : CuspidalRepresentation) (degree position : ℕ) (bound : position < degree + 1)
    (vectors : Vectors data degree) : component data degree position (residual data degree vectors) = 0 := by
  rw [residual, map_sub, primitive_cancels data degree position bound vectors, sub_self]

noncomputable def endpoint (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) : data.smooth :=
  component data degree (degree + 1) (residual data degree vectors)

/-- A finite, algebraic coboundary removes every interior coefficient of the raising component. -/
theorem residual_basis (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    residual data degree vectors = basisVector data degree (degree + 1) (endpoint data degree vectors) := by
  apply components_ext data degree
  intro position bound
  rw [component_basisVector data degree position (degree + 1) bound (by omega)]
  by_cases last : degree + 1 = position
  · subst position
    rw [ite_eq_left rfl]
    rfl
  · rw [ite_eq_right last]
    exact residual_component_zero data degree position (by omega) vectors

theorem residual_eigen (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (eigen : CoefficientRotation.shifted data degree 2 vectors = 0) :
    CoefficientRotation.shifted data degree 2 (residual data degree vectors) = 0 := by
  rw [residual, map_sub, eigen,
    CoefficientLadder.raising_zero_weight data degree _ (primitive_eigen data degree vectors eigen), sub_zero]

theorem endpoint_eigen (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (eigen : CoefficientRotation.shifted data degree 2 vectors = 0) :
    rotationOperator data (endpoint data degree vectors) = (Complex.I * (degree + 3 : ℤ)) • endpoint data degree vectors := by
  have equality := component_eigen data degree (degree + 1) 2 (by omega) (residual data degree vectors)
    (residual_eigen data degree vectors eigen)
  have endpointWeight : weight degree 2 (degree + 1) = (degree + 3 : ℤ) := by rw [weight_last]; omega
  rw [endpointWeight] at equality
  exact equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TriangularPrimitive
