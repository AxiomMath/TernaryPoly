module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.HolomorphicDominatedIntegral

@[expose] public section


open MeasureTheory Filter

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AlmostEverywhereHolomorphicIntegral

variable {Space : Type*} [MeasurableSpace Space]

theorem differentiable (measure : Measure Space) (function : ℂ → Space → ℂ)
    (measurable : ∀ parameter, Measurable (function parameter))
    (holomorphic : ∀ point, Differentiable ℂ (fun parameter => function parameter point))
    (dominated : ∀ center : ℂ, ∃ bound : Space → ℝ, Integrable bound measure ∧
      ∀ᵐ point ∂measure, ∀ parameter ∈ Metric.ball center 2, ‖function parameter point‖ ≤ bound point) :
    Differentiable ℂ (fun parameter => ∫ point, function parameter point ∂measure) := by
  intro center
  obtain ⟨bound, integrableBound, bounded⟩ := dominated center
  have atCenter : Integrable (function center) measure :=
    integrableBound.mono' (measurable center).aestronglyMeasurable
      (bounded.mono (fun point property => property center (Metric.mem_ball_self (by norm_num))))
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := function) (F' := fun parameter point => deriv (fun parameter => function parameter point) parameter)
    (s := Metric.ball center 1) (bound := fun point => 2 * bound point)
    (Metric.ball_mem_nhds center zero_lt_one)
    (Eventually.of_forall (fun parameter => (measurable parameter).aestronglyMeasurable)) atCenter
    (HolomorphicDominatedIntegral.derivative_measurable function measurable holomorphic center).aestronglyMeasurable
    (bounded.mono (fun point property parameter nearby =>
      HolomorphicDominatedIntegral.derivative_bound (fun parameter => function parameter point) (holomorphic point)
        center parameter nearby (bound point) property))
    (integrableBound.const_mul 2)
    (Eventually.of_forall (fun point parameter _ => (holomorphic point parameter).hasDerivAt))
  exact result.2.differentiableAt

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AlmostEverywhereHolomorphicIntegral
