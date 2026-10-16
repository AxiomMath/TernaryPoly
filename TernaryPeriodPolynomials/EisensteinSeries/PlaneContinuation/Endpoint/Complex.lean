module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RaisingChain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialCoordinates TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialWeights
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialLadder TernaryPeriodPolynomials.PlaneEisensteinContinuation.RaisingChain TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointComplex

theorem raising_chain (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth) :
    CoefficientLadder.raising data degree (assemble data degree (chain data vector)) =
      basisVector data degree (degree + 1) (LieOperators.raising data (chain data vector (degree + 1))) := by
  apply components_ext data degree
  intro position bound
  rw [component_raising data degree position bound, component_assemble data degree position bound,
    component_basisVector data degree position (degree + 1) bound (by omega)]
  by_cases last : degree + 1 = position
  · subst position
    rw [ite_eq_left rfl, component_above data degree (degree + 1 + 1) (by omega), smul_zero, sub_zero]
  · rw [ite_eq_right last, component_assemble data degree (position + 1) (by omega), chain_succ]
    have nonzero : (2 * (position + 1 : ℂ)) ≠ 0 := by
      apply mul_ne_zero (by norm_num)
      exact_mod_cast (show position + 1 ≠ 0 by omega)
    rw [smul_smul, mul_inv_cancel₀ nonzero, one_smul, sub_self]

theorem chain_invariant (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth)
    (eigen : rotationOperator data vector = (Complex.I * (-(degree + 1 : ℤ))) • vector) :
    operator data degree rotationMatrix (assemble data degree (chain data vector)) = 0 := by
  have coordinates (position : ℕ) (bound : position ≤ degree + 1) :
      rotationOperator data (chain data vector position) =
        (Complex.I * weight degree 0 position) • chain data vector position := by
    have equality := chain_eigen data vector (-(degree + 1 : ℤ)) (by simpa only [Int.cast_neg] using eigen) position
    have same : -(degree + 1 : ℤ) + 2 * position = weight degree 0 position := by unfold weight; omega
    rw [same] at equality
    exact equality
  simpa only [CoefficientRotation.shifted, Int.cast_zero, mul_zero, zero_smul, sub_zero] using
    assemble_eigen data degree 0 (chain data vector) coordinates

theorem exact_of_endpoint_primitive (data : CuspidalRepresentation) (degree : ℕ)
    (endpoint : data.smooth) (remaining : Vectors data degree)
    (equation : CoefficientLadder.raising data degree remaining =
      basisVector data degree (degree + 1) (LieOperators.lowering data endpoint))
    (vector : data.smooth)
    (eigen : rotationOperator data vector = (Complex.I * (-(degree + 1 : ℤ))) • vector)
    (upper : endpoint = LieOperators.raising data (chain data vector (degree + 1)))
    (lower : component data degree 0 remaining = LieOperators.lowering data vector) :
    ∃ vectors : Vectors data degree, operator data degree rotationMatrix vectors = 0 ∧
      basisVector data degree (degree + 1) endpoint = CoefficientLadder.raising data degree vectors ∧
        remaining = CoefficientLadder.lowering data degree vectors := by
  let vectors := assemble data degree (chain data vector)
  have invariant := chain_invariant data degree vector eigen
  have raised : CoefficientLadder.raising data degree vectors = basisVector data degree (degree + 1) endpoint := by
    change CoefficientLadder.raising data degree (assemble data degree (chain data vector)) = _
    rw [raising_chain, ← upper]
  refine ⟨vectors, invariant, raised.symm, ?_⟩
  have lowerRaised : CoefficientLadder.raising data degree (CoefficientLadder.lowering data degree vectors) =
      basisVector data degree (degree + 1) (LieOperators.lowering data endpoint) := by
    rw [← RelativeCoboundary.commute_on_invariant data degree vectors invariant, raised, lowering_basis_last]
  have lowerInitial : component data degree 0 (CoefficientLadder.lowering data degree vectors) =
      component data degree 0 remaining := by
    rw [component_lowering_zero]
    change LieOperators.lowering data (component data degree 0 (assemble data degree (chain data vector))) = _
    rw [component_assemble data degree 0 (by omega), chain_zero, lower]
  rw [reconstruct_of_raising data degree remaining _ equation,
    reconstruct_of_raising data degree (CoefficientLadder.lowering data degree vectors) _ lowerRaised, lowerInitial]

/-- The relative class is encoded by two genuine Hilbert vectors and one explicit ladder equation. -/
theorem exists_nontrivial_endpoint_complex {degree : ℕ} (data : InducingData degree) :
    ∃ upper lower : data.cusp.smooth,
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ upper.val ∈ fixedSubspace data.cusp level ∧ lower.val ∈ fixedSubspace data.cusp level) ∧
      rotationOperator data.cusp upper = (Complex.I * (degree + 3 : ℤ)) • upper ∧
      rotationOperator data.cusp lower = (Complex.I * (-(degree + 3 : ℤ))) • lower ∧
      LieOperators.lowering data.cusp upper = LieOperators.raising data.cusp (chain data.cusp lower (degree + 1)) ∧
      ¬ ∃ vector : data.cusp.smooth,
        rotationOperator data.cusp vector = (Complex.I * (-(degree + 1 : ℤ))) • vector ∧
          upper = LieOperators.raising data.cusp (chain data.cusp vector (degree + 1)) ∧ lower = LieOperators.lowering data.cusp vector := by
  obtain ⟨endpoint, remaining, ⟨level, openness, compactness, endpointFixed, remainingFixed⟩,
    upperEigen, remainingEigen, equation, nontrivialClass⟩ := EndpointPair.exists_endpoint_pair data
  refine ⟨endpoint, component data.cusp degree 0 remaining,
    ⟨level, openness, compactness, endpointFixed, component_fixed data.cusp degree 0 remaining level remainingFixed⟩,
    upperEigen, ?_, (last_relation data.cusp degree remaining _ equation).symm, ?_⟩
  · have equality := component_eigen data.cusp degree 0 (-2) (by omega) remaining remainingEigen
    have same : weight degree (-2) 0 = -(degree + 3 : ℤ) := by unfold weight; omega
    rw [same] at equality
    simpa only [Int.cast_neg] using equality
  · rintro ⟨vector, eigen, upper, lower⟩
    exact nontrivialClass (exact_of_endpoint_primitive data.cusp degree endpoint remaining equation vector eigen upper lower)

theorem endpoints_not_both_zero (data : CuspidalRepresentation) (degree : ℕ) (upper lower : data.smooth)
    (nontrivialClass : ¬ ∃ vector : data.smooth,
      rotationOperator data vector = (Complex.I * (-(degree + 1 : ℤ))) • vector ∧
        upper = LieOperators.raising data (chain data vector (degree + 1)) ∧ lower = LieOperators.lowering data vector) :
    upper ≠ 0 ∨ lower ≠ 0 := by
  by_contra! vanishing
  apply nontrivialClass
  refine ⟨0, ?_, ?_, ?_⟩
  · rw [map_zero, smul_zero]
  · rw [chain_zero_vector, map_zero]
    exact vanishing.1
  · rw [map_zero]
    exact vanishing.2

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointComplex
