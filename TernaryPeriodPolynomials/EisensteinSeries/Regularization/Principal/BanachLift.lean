module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.ScalarClosedGraph
public import Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspPrincipalRealization_complete_lift_continuous
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (lift : B →L[ℂ] cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) :
    Continuous (fun vector => cuspBoundedRealization cusp (lift vector).val) := by
  let composite := (cuspPrincipalRealization cusp).comp lift.toLinearMap
  apply composite.continuous_of_isClosed_graph
  have closed := (cuspPrincipalRealization_graph_isClosed cohomological).preimage
    ((lift.continuous.comp continuous_fst).prodMk continuous_snd)
  exact closed

theorem cuspPrincipalRealization_complete_lift_bound
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (lift : B →L[ℂ] cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ vector : B,
      ‖cuspBoundedRealization cusp (lift vector).val‖ ≤ constant * ‖vector‖ := by
  let realization : B →L[ℂ] BoundedContinuousFunction BinaryAdelicGL ℂ :=
    ⟨(cuspPrincipalRealization cusp).comp lift.toLinearMap,
      cuspPrincipalRealization_complete_lift_continuous cohomological lift⟩
  exact ⟨‖realization‖, realization.opNorm_nonneg, realization.le_opNorm⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
