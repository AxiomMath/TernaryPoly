module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.LowestWeightHolomorphy
public import Mathlib.NumberTheory.ModularForms.QExpansion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Filter
open scoped Manifold

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspUpperHalfForm (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cusp.smooth) (argument : BinaryAdelicGL) (point : UpperHalfPlane) : ℂ :=
  cuspHolomorphicFunction cusp weight vector argument point

theorem cohomological_upperHalfForm_mdifferentiable {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (lowering : cuspLoweringOperator cusp vector = 0) (argument : BinaryAdelicGL) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cuspUpperHalfForm cusp weight vector argument) := by
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  have differentiable :=
    (cohomological_holomorphicFunction_analyticOnNhd cohomological weight vector rotation lowering argument).differentiableOn
  apply differentiable.congr
  intro point positive
  change 0 < point.im at positive
  simp only [Function.comp_def, cuspUpperHalfForm, UpperHalfPlane.ofComplex_apply_eq_ite,
    dite_eq_left positive, UpperHalfPlane.coe_mk]

theorem cuspUpperHalfForm_zero_at_infinity (cusp : CuspidalRepresentation)
    (weight : ℝ) (weight_positive : 0 < weight) (vector : cusp.smooth) (argument : BinaryAdelicGL) :
    UpperHalfPlane.IsZeroAtImInfty (cuspUpperHalfForm cusp weight vector argument) := by
  have power_limit : Tendsto (fun height : ℝ => height ^ (-weight / 2) *
      ‖cuspBoundedRealization cusp vector‖) atTop (nhds 0) := by
    simpa only [neg_div, zero_mul] using
      (tendsto_rpow_neg_atTop (div_pos weight_positive (by norm_num : (0 : ℝ) < 2))).mul_const
        ‖cuspBoundedRealization cusp vector‖
  apply UpperHalfPlane.isZeroAtImInfty_iff.mpr
  intro epsilon epsilon_positive
  obtain ⟨threshold, bound⟩ := eventually_atTop.mp
    (power_limit.eventually (gt_mem_nhds epsilon_positive))
  refine ⟨threshold, fun point high => ?_⟩
  exact (cuspHolomorphicFunction_norm_le cusp weight vector argument point point.im_pos).trans
    (bound point.im high).le

theorem cohomological_upperHalfForm_exp_decay_of_periodic {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (weight_positive : 0 < weight)
    (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (lowering : cuspLoweringOperator cusp vector = 0) (argument : BinaryAdelicGL)
    (period : ℝ) (period_positive : 0 < period)
    (periodic : Function.Periodic
      (cuspUpperHalfForm cusp weight vector argument ∘ UpperHalfPlane.ofComplex) (period : ℂ)) :
    cuspUpperHalfForm cusp weight vector argument =O[UpperHalfPlane.atImInfty]
      (fun point => Real.exp (-2 * Real.pi * point.im / period)) := by
  have zero_at_infinity := cuspUpperHalfForm_zero_at_infinity cusp weight weight_positive vector argument
  exact zero_at_infinity.exp_decay_atImInfty period_positive periodic
    (cohomological_upperHalfForm_mdifferentiable cohomological weight vector rotation lowering argument)
    zero_at_infinity.isBoundedAtImInfty

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
