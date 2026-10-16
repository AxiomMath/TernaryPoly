module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FlatNormStrip
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ScalarSummability
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StripIntegral

theorem derivative_aestronglyMeasurable {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function : ℂ → α → ℂ)
    (measurable : ∀ parameter, AEStronglyMeasurable (function parameter) measure)
    (differentiable : ∀ argument, Differentiable ℂ (fun parameter => function parameter argument))
    (parameter : ℂ) :
    AEStronglyMeasurable (fun argument => deriv (fun z => function z argument) parameter) measure := by
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ))
    (f := fun increment argument => increment⁻¹ •
      (function (parameter + increment) argument - function parameter argument))
  · intro increment
    exact ((measurable (parameter + increment)).sub (measurable parameter)).const_smul (increment⁻¹ : ℂ)
  · exact Eventually.of_forall (fun argument =>
      (differentiable argument parameter).hasDerivAt.tendsto_slope_zero)

theorem sphere_in_strip (lower upper : ℝ) (center : ℂ)
    (lowerBound : lower < center.re) (upperBound : center.re < upper) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ parameter ∈ Metric.ball center radius,
      ∀ value ∈ Metric.sphere parameter radius, lower ≤ value.re ∧ value.re ≤ upper := by
  let radius := min (center.re - lower) (upper - center.re) / 3
  have positive : 0 < radius := div_pos (lt_min (sub_pos.mpr lowerBound)
    (sub_pos.mpr upperBound)) (by norm_num)
  refine ⟨radius, positive, ?_⟩
  intro parameter parameterMembership value valueMembership
  have distance : dist value center < 2 * radius := by
    have triangle := dist_triangle value parameter center
    rw [Metric.mem_sphere.mp valueMembership] at triangle
    have near := Metric.mem_ball.mp parameterMembership
    linarith
  rw [dist_eq_norm] at distance
  have realBound := (Complex.abs_re_le_norm (value - center)).trans_lt distance
  rw [Complex.sub_re, abs_lt] at realBound
  have left : 3 * radius ≤ center.re - lower := by
    dsimp [radius]
    linarith [min_le_left (center.re - lower) (upper - center.re)]
  have right : 3 * radius ≤ upper - center.re := by
    dsimp [radius]
    linarith [min_le_right (center.re - lower) (upper - center.re)]
  constructor <;> linarith

theorem integral_differentiableOn_strip {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function : ℂ → α → ℂ)
    (measurable : ∀ parameter, AEStronglyMeasurable (function parameter) measure)
    (differentiable : ∀ argument, Differentiable ℂ (fun parameter => function parameter argument))
    (lower upper : ℝ)
    (bounded : ∀ argument parameter, lower ≤ parameter.re → parameter.re ≤ upper →
      ‖function parameter argument‖ ≤ ‖function (lower : ℂ) argument‖ +
        ‖function (upper : ℂ) argument‖)
    (lowerIntegrable : Integrable (function (lower : ℂ)) measure)
    (upperIntegrable : Integrable (function (upper : ℂ)) measure) :
    DifferentiableOn ℂ (fun parameter => ∫ argument, function parameter argument ∂measure)
      {parameter : ℂ | lower < parameter.re ∧ parameter.re < upper} := by
  intro center membership
  obtain ⟨radius, positive, inside⟩ := sphere_in_strip lower upper center membership.1 membership.2
  have integrable : Integrable (function center) measure :=
    (lowerIntegrable.norm.add upperIntegrable.norm).mono' (measurable center)
      (Eventually.of_forall (fun argument => bounded argument center membership.1.le membership.2.le))
  have boundIntegrable : Integrable (fun argument =>
      (‖function (lower : ℂ) argument‖ + ‖function (upper : ℂ) argument‖) / radius) measure :=
    (lowerIntegrable.norm.add upperIntegrable.norm).div_const radius
  have derivativeBound : ∀ᵐ argument ∂measure, ∀ parameter ∈ Metric.ball center radius,
      ‖deriv (fun z => function z argument) parameter‖ ≤
        (‖function (lower : ℂ) argument‖ + ‖function (upper : ℂ) argument‖) / radius := by
    apply Eventually.of_forall
    intro argument parameter parameterMembership
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le positive
      (differentiable argument).diffContOnCl
    intro value valueMembership
    obtain ⟨lowerBound, upperBound⟩ := inside parameter parameterMembership value valueMembership
    exact bounded argument value lowerBound upperBound
  have derivative := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds center positive) (Eventually.of_forall measurable) integrable
    (derivative_aestronglyMeasurable measure function measurable differentiable center)
    derivativeBound boundIntegrable
    (Eventually.of_forall (fun argument parameter _ => (differentiable argument parameter).hasDerivAt))
  exact derivative.2.differentiableAt.differentiableWithinAt

theorem standard_differentiableOn_strip {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (lower upper : ℝ)
    (lowerIntegrable : Integrable (standardIntegrand extension (lower : ℂ) argument) radicalMeasure)
    (upperIntegrable : Integrable (standardIntegrand extension (upper : ℂ) argument) radicalMeasure) :
    DifferentiableOn ℂ (fun parameter =>
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure)
      {parameter : ℂ | lower < parameter.re ∧ parameter.re < upper} := by
  apply integral_differentiableOn_strip radicalMeasure
    (fun parameter => standardIntegrand extension parameter argument)
    (fun parameter => InducedContinuity.standardIntegrand_aestronglyMeasurable data extension
      parameter (flat.1 parameter) argument)
    (fun coordinates parameter => (flat.2.1 _ parameter).differentiableAt)
    lower upper _ lowerIntegrable upperIntegrable
  intro coordinates parameter lowerBound upperBound
  exact FlatNormStrip.flat_norm_strip_bound data extension flat _ lower upper parameter
    lowerBound upperBound

theorem standard_analytic_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (threshold : ℝ)
    (integrable : ∀ parameter : ℝ, threshold < parameter →
      Integrable (standardIntegrand extension (parameter : ℂ) argument) radicalMeasure)
    (parameter : ℂ) (membership : threshold < parameter.re) :
    AnalyticAt ℂ (fun parameter =>
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure) parameter := by
  let lower : ℝ := (threshold + parameter.re) / 2
  let upper : ℝ := parameter.re + 1
  have lowerThreshold : threshold < lower := by dsimp [lower]; linarith
  have upperThreshold : threshold < upper := by dsimp [upper]; linarith
  apply (standard_differentiableOn_strip data extension flat argument lower upper
    (integrable lower lowerThreshold) (integrable upper upperThreshold)).analyticAt
  apply ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
  constructor <;> dsimp [lower, upper] <;> linarith

theorem standard_analytic_of_compact_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary‖ ≤ bound)
    (argument : AdelicGL) (parameter : ℂ) (membership : -(degree : ℝ) / 2 < parameter.re) :
    AnalyticAt ℂ (fun parameter =>
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure) parameter :=
  standard_analytic_halfPlane data extension flat argument (-(degree : ℝ) / 2)
    (fun real realMembership => ScalarSummability.standard_integrable data extension flat
      bound bounded (real : ℂ) realMembership argument) parameter membership

theorem continuation_analytic_some_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation) :
    ∃ threshold : ℝ, ∀ argument parameter, threshold < parameter.re →
      AnalyticAt ℂ (fun parameter => continuation parameter argument) parameter := by
  obtain ⟨threshold, integrals⟩ := continues.2
  refine ⟨threshold, ?_⟩
  intro argument parameter membership
  have analytic := standard_analytic_halfPlane data extension flat argument threshold
    (fun real realMembership => (integrals (real : ℂ) realMembership argument).1) parameter membership
  apply analytic.congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds membership]
    with value valueMembership
  exact (integrals value valueMembership argument).2.symm

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StripIntegral
