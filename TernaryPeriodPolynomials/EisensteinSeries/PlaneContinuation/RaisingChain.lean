module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Endpoint.Pair

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialCoordinates TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialLadder
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RaisingChain

noncomputable def chain (data : CuspidalRepresentation) (vector : data.smooth) : ℕ → data.smooth
  | 0 => vector
  | position + 1 => (2 * (position + 1 : ℂ))⁻¹ • LieOperators.raising data (chain data vector position)

theorem chain_zero (data : CuspidalRepresentation) (vector : data.smooth) : chain data vector 0 = vector := rfl

theorem chain_succ (data : CuspidalRepresentation) (vector : data.smooth) (position : ℕ) :
    chain data vector (position + 1) = (2 * (position + 1 : ℂ))⁻¹ • LieOperators.raising data (chain data vector position) := rfl

theorem chain_zero_vector (data : CuspidalRepresentation) (position : ℕ) : chain data 0 position = 0 := by
  induction position with
  | zero => rfl
  | succ position inductionHypothesis => rw [chain_succ, inductionHypothesis, map_zero, smul_zero]

theorem chain_eigen (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector) (position : ℕ) :
    rotationOperator data (chain data vector position) =
      (Complex.I * (index + 2 * position : ℤ)) • chain data vector position := by
  induction position with
  | zero => simpa only [chain_zero, Nat.cast_zero, mul_zero, add_zero] using eigen
  | succ position inductionHypothesis =>
      rw [chain_succ, map_smul, LieOperators.raising_eigen data _ _ inductionHypothesis]
      have equality : index + 2 * (position : ℤ) + 2 = index + 2 * (position + 1 : ℕ) := by omega
      rw [equality]
      exact smul_comm _ _ _

theorem chain_fixed (data : CuspidalRepresentation) (vector : data.smooth) (level : Subgroup BinaryFiniteGL)
    (fixed : vector.val ∈ fixedSubspace data level) (position : ℕ) : (chain data vector position).val ∈ fixedSubspace data level := by
  induction position with
  | zero => exact fixed
  | succ position inductionHypothesis =>
      exact (fixedSubspace data level).smul_mem _ (raising_preserves_fixed data level _ inductionHypothesis)

theorem component_succ_of_raising (data : CuspidalRepresentation) (degree position : ℕ) (bound : position < degree + 1)
    (vectors : Vectors data degree) (value : data.smooth)
    (equation : CoefficientLadder.raising data degree vectors = basisVector data degree (degree + 1) value) :
    component data degree (position + 1) vectors =
      (2 * (position + 1 : ℂ))⁻¹ • LieOperators.raising data (component data degree position vectors) := by
  have equality := congrArg (component data degree position) equation
  rw [component_raising data degree position (by omega),
    component_basisVector data degree position (degree + 1) (by omega) (by omega), ite_eq_right (by omega)] at equality
  have relation := sub_eq_zero.mp equality
  have nonzero : (2 * (position + 1 : ℂ)) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact_mod_cast (show position + 1 ≠ 0 by omega)
  apply (smul_right_inj (M := data.smooth) (r := (2 * (position + 1 : ℂ))) nonzero).mp
  rw [smul_smul, mul_inv_cancel₀ nonzero, one_smul]
  exact relation.symm

theorem components_of_raising (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (value : data.smooth)
    (equation : CoefficientLadder.raising data degree vectors = basisVector data degree (degree + 1) value)
    (position : ℕ) (bound : position ≤ degree + 1) :
    component data degree position vectors = chain data (component data degree 0 vectors) position := by
  induction position with
  | zero => rfl
  | succ position inductionHypothesis =>
      rw [component_succ_of_raising data degree position (by omega) vectors value equation,
        inductionHypothesis (by omega), chain_succ]

theorem reconstruct_of_raising (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (value : data.smooth)
    (equation : CoefficientLadder.raising data degree vectors = basisVector data degree (degree + 1) value) :
    vectors = assemble data degree (chain data (component data degree 0 vectors)) := by
  apply components_ext data degree
  intro position bound
  rw [components_of_raising data degree vectors value equation position bound, component_assemble data degree position bound]

theorem last_relation (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (value : data.smooth)
    (equation : CoefficientLadder.raising data degree vectors = basisVector data degree (degree + 1) value) :
    LieOperators.raising data (chain data (component data degree 0 vectors) (degree + 1)) = value := by
  have equality := congrArg (component data degree (degree + 1)) equation
  rw [component_raising data degree (degree + 1) (by omega),
    component_above data degree (degree + 1 + 1) (by omega), smul_zero, sub_zero,
    component_basisVector data degree (degree + 1) (degree + 1) (by omega) (by omega), ite_eq_left rfl,
    components_of_raising data degree vectors value equation (degree + 1) (by omega)] at equality
  exact equality

theorem component_lowering_basis_zero (data : CuspidalRepresentation) (degree position : ℕ)
    (bound : position ≤ degree + 1) (vector : data.smooth) :
    component data degree 0 (CoefficientLadder.lowering data degree (basisVector data degree position vector)) =
      if position = 0 then LieOperators.lowering data vector else 0 := by
  by_cases last : position = degree + 1
  · subst position
    rw [lowering_basis_last, component_basisVector data degree 0 (degree + 1) (by omega) (by omega)]
  · rw [lowering_basis data degree position (by omega), map_add, map_smul,
      component_basisVector data degree 0 position (by omega) bound,
      component_basisVector data degree 0 (position + 1) (by omega) (by omega)]
    simp

theorem component_lowering_zero (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    component data degree 0 (CoefficientLadder.lowering data degree vectors) =
      LieOperators.lowering data (component data degree 0 vectors) := by
  have equality := congrArg (fun value : Vectors data degree => component data degree 0 (CoefficientLadder.lowering data degree value))
    (reconstruct data degree vectors)
  simp only [map_sum] at equality
  have terms : (∑ position ∈ Finset.range (degree + 2), component data degree 0
      (CoefficientLadder.lowering data degree (basisVector data degree position (component data degree position vectors)))) =
      ∑ position ∈ Finset.range (degree + 2), if position = 0 then LieOperators.lowering data (component data degree position vectors) else 0 := by
    apply Finset.sum_congr rfl
    intro position membership
    exact component_lowering_basis_zero data degree position (by have := Finset.mem_range.mp membership; omega) _
  rw [terms, Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr (by omega))] at equality
  exact equality.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RaisingChain
