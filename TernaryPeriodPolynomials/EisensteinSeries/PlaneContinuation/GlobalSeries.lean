module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.GlobalBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.Series

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalSeries

theorem summand_bound_on_strip {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL)
    (reference : ℂ) (upperBound : ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ,
      reference.re ≤ parameter.re → parameter.re ≤ upperBound → ∀ flag : Flags .plane,
      ‖eisensteinSummand sectionFamily parameter basePoint flag‖ ≤
        bound * ‖eisensteinSummand sectionFamily reference basePoint flag‖ := by
  obtain ⟨heightBound, heightProperty⟩ := TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicHeight.height_flag_boundedAbove basePoint
  refine ⟨Real.exp ((upperBound - reference.re) * max 0 heightBound), (Real.exp_pos _).le,
    fun parameter lowerParameter upperParameter flag => ?_⟩
  rw [eisensteinSummand_change_parameter flatSection basePoint flag parameter reference,
    norm_mul, Complex.norm_exp]
  have realExponent : ((parameter - reference) *
      (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ)).re =
      (parameter.re - reference.re) * height (rationalGroup flag.out⁻¹ * basePoint) := by simp
  rw [realExponent]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left ((heightProperty flag).trans (le_max_right _ _))
    (sub_nonneg.mpr lowerParameter)).trans
    (mul_le_mul_of_nonneg_right (sub_le_sub_right upperParameter _) (le_max_left _ _))

theorem summable_of_re_le {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference basePoint))
    (parameter : ℂ) (parameterBound : reference.re ≤ parameter.re) :
    Summable (eisensteinSummand sectionFamily parameter basePoint) := by
  obtain ⟨bound, _, boundProperty⟩ := summand_bound_on_strip flatSection basePoint reference parameter.re
  exact (convergence.norm.mul_left bound).of_norm_bounded
    (boundProperty parameter parameterBound le_rfl)

theorem uniformly_on_strip {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference basePoint))
    (upperBound : ℝ) :
    TendstoUniformlyOn
      (fun finiteSet : Finset (Flags .plane) => fun parameter =>
        ∑ flag ∈ finiteSet, eisensteinSummand sectionFamily parameter basePoint flag)
      (fun parameter => literalSum sectionFamily parameter basePoint)
      Filter.atTop {parameter : ℂ | reference.re ≤ parameter.re ∧ parameter.re ≤ upperBound} := by
  obtain ⟨bound, _, boundProperty⟩ := summand_bound_on_strip flatSection basePoint reference upperBound
  apply tendstoUniformlyOn_tsum (convergence.norm.mul_left bound)
  intro flag parameter membership
  exact boundProperty parameter membership.1 membership.2 flag

theorem analytic_of_summable {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference basePoint)) :
    AnalyticOnNhd ℂ (fun parameter => literalSum sectionFamily parameter basePoint)
      {parameter : ℂ | reference.re < parameter.re} := by
  intro parameter parameterBound
  let strip : Set ℂ := {value | reference.re < value.re ∧ value.re < parameter.re + 1}
  have openness : IsOpen strip :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have inclusion : strip ⊆
      {value : ℂ | reference.re ≤ value.re ∧ value.re ≤ parameter.re + 1} := by
    intro value membership
    exact ⟨membership.1.le, membership.2.le⟩
  have uniform := (uniformly_on_strip flatSection basePoint reference convergence
    (parameter.re + 1)).mono inclusion
  have differentiability : DifferentiableOn ℂ
      (fun value => literalSum sectionFamily value basePoint) strip := by
    apply uniform.tendstoLocallyUniformlyOn.differentiableOn _ openness
    apply Filter.Eventually.of_forall
    intro finiteSet
    apply DifferentiableOn.fun_sum
    intro flag _ value _
    exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.flatSection_summand_analytic flatSection basePoint flag value).differentiableAt.differentiableWithinAt
  exact differentiability.analyticOnNhd openness parameter ⟨parameterBound, by linarith⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalSeries
