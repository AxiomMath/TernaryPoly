module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.Parameter
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Real.Cardinality

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarParameter

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries

noncomputable def literalSum (sectionFamily : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (basePoint : AdelicGL) : ℂ :=
  ∑' flag : Flags .plane, eisensteinSummand sectionFamily parameter basePoint flag

theorem summable_one_of_re_le {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference 1))
    (parameter : ℂ) (parameterBound : reference.re ≤ parameter.re) :
    Summable (eisensteinSummand sectionFamily parameter 1) :=
  convergence.norm.of_norm_bounded (fun flag =>
    norm_eisensteinSummand_one_antitone flatSection flag parameter reference parameterBound)

theorem hasSum_one_of_re_le {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference 1))
    (parameter : ℂ) (parameterBound : reference.re ≤ parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter 1) (literalSum sectionFamily parameter 1) :=
  (summable_one_of_re_le flatSection reference convergence parameter parameterBound).hasSum

theorem uniformly_one_of_summable {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference 1)) :
    TendstoUniformlyOn
      (fun finiteSet : Finset (Flags .plane) => fun parameter =>
        ∑ flag ∈ finiteSet, eisensteinSummand sectionFamily parameter 1 flag)
      (fun parameter => literalSum sectionFamily parameter 1)
      Filter.atTop {parameter : ℂ | reference.re ≤ parameter.re} :=
  tendstoUniformlyOn_tsum convergence.norm (fun flag parameter parameterBound =>
    norm_eisensteinSummand_one_antitone flatSection flag parameter reference parameterBound)

theorem analytic_one_of_summable {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference 1)) :
    AnalyticOnNhd ℂ (fun parameter => literalSum sectionFamily parameter 1)
      {parameter : ℂ | reference.re < parameter.re} := by
  have openness : IsOpen {parameter : ℂ | reference.re < parameter.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have inclusion : {parameter : ℂ | reference.re < parameter.re} ⊆
      {parameter : ℂ | reference.re ≤ parameter.re} := by
    intro parameter membership
    exact (show reference.re < parameter.re from membership).le
  have uniform := (uniformly_one_of_summable flatSection reference convergence).mono inclusion
  apply DifferentiableOn.analyticOnNhd _ openness
  apply uniform.tendstoLocallyUniformlyOn.differentiableOn _ openness
  apply Filter.Eventually.of_forall
  intro finiteSet
  apply DifferentiableOn.fun_sum
  intro flag _ parameter _
  exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.flatSection_summand_analytic flatSection 1 flag parameter).differentiableAt.differentiableWithinAt

theorem summand_bound_on_strip {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3)
    (reference : ℂ) (upperBound : ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ,
      reference.re ≤ parameter.re → parameter.re ≤ upperBound → ∀ flag : Flags .plane,
      ‖eisensteinSummand sectionFamily parameter (atInfinity realMatrix) flag‖ ≤
        bound * ‖eisensteinSummand sectionFamily reference (atInfinity realMatrix) flag‖ := by
  obtain ⟨heightBound, nonnegativeHeightBound, heightProperty⟩ := flagHeight_boundedAbove realMatrix
  refine ⟨Real.exp ((upperBound - reference.re) * heightBound), (Real.exp_pos _).le,
    fun parameter lowerParameter upperParameter flag => ?_⟩
  rw [norm_eisensteinSummand_atInfinity_change_parameter flatSection realMatrix flag
    parameter reference]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left (heightProperty flag)
    (sub_nonneg.mpr lowerParameter)).trans
    (mul_le_mul_of_nonneg_right (sub_le_sub_right upperParameter _) nonnegativeHeightBound)

theorem summable_atInfinity_of_re_le {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference (atInfinity realMatrix)))
    (parameter : ℂ) (parameterBound : reference.re ≤ parameter.re) :
    Summable (eisensteinSummand sectionFamily parameter (atInfinity realMatrix)) := by
  obtain ⟨bound, _, boundProperty⟩ := summand_bound_on_strip flatSection realMatrix reference
    parameter.re
  exact (convergence.norm.mul_left bound).of_norm_bounded
    (boundProperty parameter parameterBound le_rfl)

theorem uniformly_atInfinity_on_strip {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference (atInfinity realMatrix)))
    (upperBound : ℝ) :
    TendstoUniformlyOn
      (fun finiteSet : Finset (Flags .plane) => fun parameter =>
        ∑ flag ∈ finiteSet, eisensteinSummand sectionFamily parameter (atInfinity realMatrix) flag)
      (fun parameter => literalSum sectionFamily parameter (atInfinity realMatrix))
      Filter.atTop {parameter : ℂ | reference.re ≤ parameter.re ∧ parameter.re ≤ upperBound} := by
  obtain ⟨bound, _, boundProperty⟩ := summand_bound_on_strip flatSection realMatrix reference upperBound
  apply tendstoUniformlyOn_tsum (convergence.norm.mul_left bound)
  intro flag parameter membership
  exact boundProperty parameter membership.1 membership.2 flag

theorem analytic_atInfinity_of_summable {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (realMatrix : RealGL3) (reference : ℂ)
    (convergence : Summable (eisensteinSummand sectionFamily reference (atInfinity realMatrix))) :
    AnalyticOnNhd ℂ (fun parameter => literalSum sectionFamily parameter (atInfinity realMatrix))
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
  have uniform := (uniformly_atInfinity_on_strip flatSection realMatrix reference convergence
    (parameter.re + 1)).mono inclusion
  have differentiability : DifferentiableOn ℂ
      (fun value => literalSum sectionFamily value (atInfinity realMatrix)) strip := by
    apply uniform.tendstoLocallyUniformlyOn.differentiableOn _ openness
    apply Filter.Eventually.of_forall
    intro finiteSet
    apply DifferentiableOn.fun_sum
    intro flag _ value _
    exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.flatSection_summand_analytic flatSection
      (atInfinity realMatrix) flag value).differentiableAt.differentiableWithinAt
  exact differentiability.analyticOnNhd openness parameter ⟨parameterBound, by linarith⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries
