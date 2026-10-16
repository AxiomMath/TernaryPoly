module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.IntegrandDomination
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.JointContinuity

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactScalarConvergence

theorem standard_integrable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) :
    Integrable (standardIntegrand extension parameter argument) radicalMeasure := by
  obtain ⟨bound, _, bounded⟩ :=
    CompactScalarRealization.induced_uniform_binary_bound data cohomologicalPoint
      (extension cohomologicalPoint) (flat.1 cohomologicalPoint)
  exact ScalarSummability.standard_integrable data extension flat bound bounded
    parameter halfPlane argument

theorem eisenstein_summable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) :
    Summable (eisensteinSummand extension parameter argument) := by
  obtain ⟨bound, _, bounded⟩ :=
    CompactScalarRealization.induced_uniform_binary_bound data cohomologicalPoint
      (extension cohomologicalPoint) (flat.1 cohomologicalPoint)
  exact CompactMajorant.summable data extension flat bound bounded
    parameter halfPlane argument

theorem eisenstein_constantTerm {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) (eisenstein : AdelicGL → ℂ)
    (sums : ∀ value, HasSum (eisensteinSummand extension parameter value)
      (eisenstein value)) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      eisenstein (lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure) =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates
        ∂radicalMeasure := by
  obtain ⟨bound, _, bounded⟩ :=
    CompactScalarRealization.induced_uniform_binary_bound data cohomologicalPoint
      (extension cohomologicalPoint) (flat.1 cohomologicalPoint)
  exact ScalarSummability.eisenstein_constantTerm data extension flat bound bounded
    parameter halfPlane argument eisenstein sums

theorem standard_joint_continuousAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    ContinuousAt (fun pair : ℂ × AdelicGL =>
      ∫ coordinates, standardIntegrand extension pair.1 pair.2 coordinates
        ∂radicalMeasure) (parameter, argument) := by
  obtain ⟨bound, _, bounded⟩ :=
    CompactScalarRealization.induced_uniform_binary_bound data cohomologicalPoint
      (extension cohomologicalPoint) (flat.1 cohomologicalPoint)
  exact StandardJointContinuity.standard_continuousAt data extension flat
    bound bounded parameter argument halfPlane

theorem standard_has_analytic_domination {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) :
    MeromorphicParameterIntegral.HasAnalyticDomination radicalMeasure
      (fun value coordinates => standardIntegrand extension value argument coordinates)
      parameter := by
  let radius : ℝ := (parameter.re + (degree : ℝ) / 2) / 2
  let lower : ℝ := parameter.re - radius
  let upper : ℝ := parameter.re + radius
  let neighborhood := Metric.ball parameter radius
  let majorant : Adeles × Adeles → ℝ := fun coordinates =>
    ‖standardIntegrand extension (lower : ℂ) argument coordinates‖ +
      ‖standardIntegrand extension (upper : ℂ) argument coordinates‖
  have radiusPositive : 0 < radius := by dsimp [radius]; linarith
  have lowerHalfPlane : -(degree : ℝ) / 2 < lower := by
    dsimp [lower, radius]
    linarith
  have upperHalfPlane : -(degree : ℝ) / 2 < upper := by
    dsimp [upper, radius]
    linarith
  have majorantIntegrable : Integrable majorant radicalMeasure := by
    exact (standard_integrable data extension flat (lower : ℂ) lowerHalfPlane
      argument).norm.add
        (standard_integrable data extension flat (upper : ℂ) upperHalfPlane argument).norm
  have realBounds : ∀ value, value ∈ neighborhood →
      lower ≤ value.re ∧ value.re ≤ upper := by
    intro value membership
    have distance : dist value parameter < radius := Metric.mem_ball.mp membership
    have absoluteBound : |value.re - parameter.re| < radius := by
      calc
        |value.re - parameter.re| = |(value - parameter).re| := by rw [Complex.sub_re]
        _ ≤ ‖value - parameter‖ := Complex.abs_re_le_norm _
        _ < radius := by simpa [dist_eq_norm] using distance
    rw [abs_lt] at absoluteBound
    constructor <;> dsimp [lower, upper] <;> linarith
  refine ⟨neighborhood, majorant, Metric.isOpen_ball,
    Metric.mem_ball_self radiusPositive, ?_, ?_, majorantIntegrable, ?_⟩
  · intro value
    exact InducedContinuity.standardIntegrand_aestronglyMeasurable data extension value
      (flat.1 value) argument
  · intro coordinates value membership
    exact (flat.2.1
      (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument)
      value).differentiableAt.differentiableWithinAt
  · intro coordinates value membership
    have intervalBounds := realBounds value membership
    exact FlatNormStrip.flat_norm_strip_bound data extension flat
      (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument)
      lower upper value intervalBounds.1 intervalBounds.2

theorem standard_analyticAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) :
    AnalyticAt ℂ (fun value =>
      ∫ coordinates, standardIntegrand extension value argument coordinates
        ∂radicalMeasure) parameter := by
  exact MeromorphicParameterIntegral.integral_analyticAt_of_domination _ _ parameter
    (standard_has_analytic_domination data extension flat parameter halfPlane argument)

theorem standard_endpoint_integrable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (degreeBound : 4 ≤ degree) (argument : AdelicGL) :
    Integrable (standardIntegrand extension cohomologicalPoint argument) radicalMeasure := by
  have degreeAsReal : (4 : ℝ) ≤ (degree : ℝ) := by exact_mod_cast degreeBound
  apply standard_integrable data extension flat cohomologicalPoint
  norm_num [cohomologicalPoint]
  linarith

theorem standard_endpoint_analyticAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (degreeBound : 4 ≤ degree) (argument : AdelicGL) :
    AnalyticAt ℂ (fun value =>
      ∫ coordinates, standardIntegrand extension value argument coordinates
        ∂radicalMeasure) cohomologicalPoint := by
  have degreeAsReal : (4 : ℝ) ≤ (degree : ℝ) := by exact_mod_cast degreeBound
  apply standard_analyticAt data extension flat cohomologicalPoint
  norm_num [cohomologicalPoint]
  linarith

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactScalarConvergence
