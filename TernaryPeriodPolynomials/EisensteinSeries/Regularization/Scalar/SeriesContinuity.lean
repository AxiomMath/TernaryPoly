module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.FlagIntegrability
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.VectorKernelContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem continuousOn_tsum_of_locallyUniform
    {I X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F]
    {family : I → X → F} {domain : Set X}
    (uniform : SummableLocallyUniformlyOn family domain)
    (continuous : ∀ index, ContinuousOn (family index) domain) :
    ContinuousOn (fun point => ∑' index, family index point) domain := by
  apply uniform.hasSumLocallyUniformlyOn.continuousOn
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro indices
  exact continuousOn_finsetSum indices (fun index _ => continuous index)

theorem normalized_scalar_flag_sum_locally_uniform
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    SummableLocallyUniformlyOn
      (fun flag (input : ℂ × AdelicGL) =>
        eisensteinSummand (unitaryNormalize degree family) input.1 input.2 flag)
      {input : ℂ × AdelicGL | 3 / 2 < input.1.re} := by
  apply SummableLocallyUniformlyOn_of_locally_bounded
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst))
  intro domain contained compact
  obtain ⟨majorant, summable, bounded⟩ := normalized_scalar_flag_compact_majorant flat
    (normalizedScalarProfile_compact_bound flat) (Prod.fst '' domain) (Prod.snd '' domain)
    (compact.image continuous_fst) (compact.image continuous_snd)
    (by rintro parameter ⟨input, member, rfl⟩; exact contained member)
  refine ⟨majorant, summable, ?_⟩
  intro flag input member
  exact bounded input.1 ⟨input, member, rfl⟩ input.2 ⟨input, member, rfl⟩ flag

theorem normalized_scalar_flag_sum_joint_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ContinuousOn
      (fun input : ℂ × AdelicGL => ∑' flag,
        eisensteinSummand (unitaryNormalize degree family) input.1 input.2 flag)
      {input : ℂ × AdelicGL | 3 / 2 < input.1.re} := by
  apply continuousOn_tsum_of_locallyUniform (normalized_scalar_flag_sum_locally_uniform flat)
  intro flag
  apply Continuous.continuousOn
  have input_continuous : Continuous (fun input : ℂ × AdelicGL =>
      (input.1, rationalGroup flag.out⁻¹ * input.2)) :=
    continuous_fst.prodMk ((continuous_const (y := rationalGroup flag.out⁻¹)).mul continuous_snd)
  change Continuous (fun input : ℂ × AdelicGL =>
    unitaryNormalize degree family input.1 (rationalGroup flag.out⁻¹ * input.2))
  have composed := (unitaryNormalize_joint_continuous flat).comp input_continuous
  dsimp only [Function.comp_def] at composed
  exact composed

theorem scalar_flag_sum_eq_normalized
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : -(degree : ℝ) / 2 < parameter.re) (matrix : AdelicGL) :
    (∑' flag, eisensteinSummand family parameter matrix flag) =
      normPower (GeneralLinearGroup.det matrix) (((degree : ℂ) + 3) / 3) *
        ∑' flag, eisensteinSummand (unitaryNormalize degree family)
          (parameter + ((degree : ℂ) + 3) / 2) matrix flag := by
  have normalized := (normalized_scalar_sum_analytic flat matrix).2 _ (shifted_parameter_large large)
  have scaled := normalized.hasSum.mul_left
    (normPower (GeneralLinearGroup.det matrix) (((degree : ℂ) + 3) / 3))
  have identity : (fun flag => normPower (GeneralLinearGroup.det matrix) (((degree : ℂ) + 3) / 3) *
        eisensteinSummand (unitaryNormalize degree family)
          (parameter + ((degree : ℂ) + 3) / 2) matrix flag) =
      eisensteinSummand family parameter matrix :=
    funext (fun flag => (eisensteinSummand_of_unitaryNormalize degree family parameter matrix flag).symm)
  rw [identity] at scaled
  exact (scalar_flag_summable flat parameter large matrix).hasSum.unique scaled

theorem scalar_flag_sum_joint_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ContinuousOn (fun input : ℂ × AdelicGL => ∑' flag, eisensteinSummand family input.1 input.2 flag)
      {input : ℂ × AdelicGL | -(degree : ℝ) / 2 < input.1.re} := by
  have composed : ContinuousOn (fun input : ℂ × AdelicGL => ∑' flag,
      eisensteinSummand (unitaryNormalize degree family)
        (input.1 + ((degree : ℂ) + 3) / 2) input.2 flag)
      {input : ℂ × AdelicGL | -(degree : ℝ) / 2 < input.1.re} :=
    (normalized_scalar_flag_sum_joint_continuous flat).comp
    ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn
    (fun _ member => shifted_parameter_large member)
  have factor_continuous : Continuous
      (fun input : ℂ × AdelicGL => normPower (GeneralLinearGroup.det input.2) (((degree : ℂ) + 3) / 3)) :=
    normPower_continuous.comp ((adelicDet_continuous.comp continuous_snd).prodMk continuous_const)
  apply (factor_continuous.continuousOn.mul composed).congr
  intro input member
  exact scalar_flag_sum_eq_normalized flat input.1 member input.2

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
