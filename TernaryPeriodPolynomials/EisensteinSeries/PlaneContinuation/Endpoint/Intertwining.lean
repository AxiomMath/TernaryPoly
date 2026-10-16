module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Endpoint.Complex

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RaisingChain TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialCoordinates
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialLadder TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointIntertwining

theorem chain_add (data : CuspidalRepresentation) (first second : data.smooth) (position : ℕ) :
    chain data (first + second) position = chain data first position + chain data second position := by
  induction position with
  | zero => rfl
  | succ position inductionHypothesis =>
      rw [chain_succ, inductionHypothesis, map_add, smul_add, chain_succ, chain_succ]

theorem chain_smul (data : CuspidalRepresentation) (scalar : ℂ) (vector : data.smooth) (position : ℕ) :
    chain data (scalar • vector) position = scalar • chain data vector position := by
  induction position with
  | zero => rfl
  | succ position inductionHypothesis =>
      rw [chain_succ, inductionHypothesis, map_smul, chain_succ, smul_comm]

theorem chain_raising (data : CuspidalRepresentation) (vector : data.smooth) (position : ℕ) :
    chain data (raising data vector) position = raising data (chain data vector position) := by
  induction position with
  | zero => rfl
  | succ position inductionHypothesis =>
      rw [chain_succ, inductionHypothesis, chain_succ, map_smul]

/-- At the middle weight the endpoint differential commutes with lowering. -/
theorem lowering_endpoint (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth)
    (eigen : rotationOperator data vector = (Complex.I * (-(degree + 1 : ℤ))) • vector) :
    lowering data (raising data (chain data vector (degree + 1))) =
      raising data (chain data (lowering data vector) (degree + 1)) := by
  let vectors := assemble data degree (chain data vector)
  have invariant := EndpointComplex.chain_invariant data degree vector eigen
  have equation : CoefficientLadder.raising data degree (CoefficientLadder.lowering data degree vectors) =
      basisVector data degree (degree + 1) (lowering data (raising data (chain data vector (degree + 1)))) := by
    rw [← RelativeCoboundary.commute_on_invariant data degree vectors invariant]
    change CoefficientLadder.lowering data degree
      (CoefficientLadder.raising data degree (assemble data degree (chain data vector))) = _
    rw [EndpointComplex.raising_chain, lowering_basis_last]
  have equality := last_relation data degree (CoefficientLadder.lowering data degree vectors) _ equation
  rw [component_lowering_zero] at equality
  change raising data (chain data (lowering data (component data degree 0
    (assemble data degree (chain data vector)))) (degree + 1)) = _ at equality
  rw [component_assemble data degree 0 (by omega), chain_zero] at equality
  exact equality.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointIntertwining
