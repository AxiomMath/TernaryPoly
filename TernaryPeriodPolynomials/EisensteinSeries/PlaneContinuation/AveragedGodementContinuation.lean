module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.ThetaIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AlmostEverywhereHolomorphicIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ParametricGodementContinuation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UnipotentCompactDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzRegularization TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementScalingFactor
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentCompactDomain

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragedGodementContinuation

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem total_differentiable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (zeroValue : ∀ parameter, tests parameter 0 = 0)
    (zeroFourier : ∀ parameter, FourierTransform.fourier (tests parameter) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) :
    Differentiable ℂ (fun parameter => average (fun value => VectorThetaIntegral.total data family
      (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset)) value parameter) point) := by
  apply AlmostEverywhereHolomorphicIntegral.differentiable parameterMeasure
    (fun parameter pair => VectorThetaIntegral.total data family
      (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset))
        (planeUnipotent pair.1 pair.2 * point) parameter)
  · intro parameter
    exact (CompactThetaIntegral.total_measurable data family continuous (tests parameter) _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) parameter).comp
      (PlaneChartContinuity.planeUnipotent_continuous.mul continuous_const).measurable
  · intro pair
    exact UniformVectorIntegral.differentiable data family continuous tests holomorphic bounded zeroValue zeroFourier
      finiteScale offset (planeUnipotent pair.1 pair.2 * point)
  · intro center
    let points := (fun pair : Adeles × Adeles => planeUnipotent pair.1 pair.2 * point) '' (closureBox ×ˢ closureBox)
    have compact : IsCompact points := (closureBox_compact.prod closureBox_compact).image
      (PlaneChartContinuity.planeUnipotent_continuous.mul continuous_const)
    obtain ⟨bound, _, bounds⟩ := CompactThetaIntegral.total_bound data family continuous tests holomorphic bounded
      zeroValue zeroFourier finiteScale offset points compact (Metric.closedBall center 2) (isCompact_closedBall center 2)
    refine ⟨fun _ => bound, integrable_const _, ?_⟩
    filter_upwards [ae_mem_domain] with pair membership
    intro parameter parameterMembership
    exact bounds parameter (Metric.ball_subset_closedBall parameterMembership) _
      ⟨pair, ⟨domain_subset membership.1, domain_subset membership.2⟩, rfl⟩

theorem total_integrable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (zeroValue : ∀ parameter, tests parameter 0 = 0)
    (zeroFourier : ∀ parameter, FourierTransform.fourier (tests parameter) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (parameter : ℂ) :
    Integrable (fun pair : Adeles × Adeles => VectorThetaIntegral.total data family
      (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset))
        (planeUnipotent pair.1 pair.2 * point) parameter) parameterMeasure := by
  let points := (fun pair : Adeles × Adeles => planeUnipotent pair.1 pair.2 * point) '' (closureBox ×ˢ closureBox)
  have compact : IsCompact points := (closureBox_compact.prod closureBox_compact).image
    (PlaneChartContinuity.planeUnipotent_continuous.mul continuous_const)
  obtain ⟨bound, _, bounds⟩ := CompactThetaIntegral.total_bound data family continuous tests holomorphic bounded
    zeroValue zeroFourier finiteScale offset points compact {parameter} isCompact_singleton
  have measurable := (CompactThetaIntegral.total_measurable data family continuous (tests parameter) _
    (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) parameter).comp
    (PlaneChartContinuity.planeUnipotent_continuous.mul (continuous_const (y := point))).measurable
  apply (integrable_const (μ := parameterMeasure) bound).mono' measurable.aestronglyMeasurable
  filter_upwards [ae_mem_domain] with pair membership
  exact bounds parameter (Set.mem_singleton _) _
    ⟨pair, ⟨domain_subset membership.1, domain_subset membership.2⟩, rfl⟩

theorem integrable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (parameter : ℂ) :
    Integrable (fun pair : Adeles × Adeles => VectorGodementContinuation.continuation data family
      (tests parameter) finiteScale offset parameter (planeUnipotent pair.1 pair.2 * point)) parameterMeasure := by
  have totalIntegrable := total_integrable data family continuous
    (fun parameter => regularize (tests parameter))
    (RegularizedTestFamilies.pointwise_differentiable tests holomorphic)
    (fun compact compactIs => RegularizedTestFamilies.family_bounded tests compact (bounded compact compactIs))
    (fun parameter => regularize_zero (tests parameter))
    (fun parameter => regularize_fourier_zero (tests parameter)) finiteScale offset point parameter
  simpa only [VectorGodementContinuation.continuation, VectorThetaIntegral.continuation,
    map_mul, GodementIntegral.det_planeUnipotent, one_mul] using
    (totalIntegrable.const_mul (GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point))).div_const
      (regularizationFactor data parameter)

omit [CompleteSpace Source] in
theorem average_eq {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (tests : ℂ → SchwartzMap RealSpace Source)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (parameter : ℂ) :
    average (fun value => VectorGodementContinuation.continuation data family (tests parameter)
      finiteScale offset parameter value) point =
    (GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point) *
      average (fun value => VectorThetaIntegral.total data family
        (BanachAdelicTheta.tensorTest (regularize (tests parameter))
          (RectangularAdelicPoisson.finiteTest finiteScale offset)) value parameter) point) /
      regularizationFactor data parameter := by
  simp only [PlaneConstantTerm.average, VectorGodementContinuation.continuation, VectorThetaIntegral.continuation,
    map_mul, GodementIntegral.det_planeUnipotent, one_mul]
  rw [integral_div, integral_const_mul]

theorem meromorphic {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (parameter : ℂ) :
    MeromorphicAt (fun parameter => average (fun value => VectorGodementContinuation.continuation data family
      (tests parameter) finiteScale offset parameter value) point) parameter := by
  have integralDifferentiable := total_differentiable data family continuous
    (fun parameter => regularize (tests parameter))
    (RegularizedTestFamilies.pointwise_differentiable tests holomorphic)
    (fun compact compactIs => RegularizedTestFamilies.family_bounded tests compact (bounded compact compactIs))
    (fun parameter => regularize_zero (tests parameter))
    (fun parameter => regularize_fourier_zero (tests parameter)) finiteScale offset point
  have numerator := (ZeroConstantThetaIntegral.outer_differentiable data (GeneralLinearGroup.det point)).mul integralDifferentiable
  have result := (numerator.analyticAt parameter).meromorphicAt.div
    ((factor_differentiable data).analyticAt parameter).meromorphicAt
  exact result.congr (Filter.Eventually.of_forall (fun value => (average_eq data family tests finiteScale offset point value).symm))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragedGodementContinuation
