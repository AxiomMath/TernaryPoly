module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.MeromorphicParameterIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.StripIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardIntegrandDomination

theorem original_integrand_has_analytic_domination {degree : ℕ}
    (data : InducingData degree) (extension : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension) (bound : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact) binary‖ ≤ bound)
    (degreeBound : 4 ≤ degree) (argument : AdelicGL) :
    MeromorphicParameterIntegral.HasAnalyticDomination
      (radicalMeasure.restrict (additiveDomain ×ˢ additiveDomain))
      (fun parameter coordinates => standardIntegrand extension parameter argument coordinates)
      cohomologicalPoint := by
  let neighborhood := Metric.ball cohomologicalPoint (1 / 4 : ℝ)
  let majorant : Adeles × Adeles → ℝ := fun coordinates =>
    ‖standardIntegrand extension ((-7 / 4 : ℝ) : ℂ) argument coordinates‖ +
      ‖standardIntegrand extension ((-5 / 4 : ℝ) : ℂ) argument coordinates‖
  have degreeAsReal : (4 : ℝ) ≤ (degree : ℝ) := by
    exact_mod_cast degreeBound
  have lowerHalfPlane : -(degree : ℝ) / 2 < (-7 / 4 : ℝ) := by
    linarith
  have upperHalfPlane : -(degree : ℝ) / 2 < (-5 / 4 : ℝ) := by
    linarith
  have lowerIntegrable :
      Integrable (standardIntegrand extension ((-7 / 4 : ℝ) : ℂ) argument) radicalMeasure :=
    ScalarSummability.standard_integrable data extension flat bound bounded
      ((-7 / 4 : ℝ) : ℂ) lowerHalfPlane argument
  have upperIntegrable :
      Integrable (standardIntegrand extension ((-5 / 4 : ℝ) : ℂ) argument) radicalMeasure :=
    ScalarSummability.standard_integrable data extension flat bound bounded
      ((-5 / 4 : ℝ) : ℂ) upperHalfPlane argument
  have majorantIntegrable :
      Integrable majorant (radicalMeasure.restrict (additiveDomain ×ˢ additiveDomain)) := by
    dsimp [majorant]
    exact (lowerIntegrable.norm.add upperIntegrable.norm).restrict
  have realBounds : ∀ parameter, parameter ∈ neighborhood →
      (-7 / 4 : ℝ) ≤ parameter.re ∧ parameter.re ≤ (-5 / 4 : ℝ) := by
    intro parameter parameterMembership
    have distance : dist parameter cohomologicalPoint < (1 / 4 : ℝ) :=
      Metric.mem_ball.mp parameterMembership
    have absoluteBound : |parameter.re + 3 / 2| < (1 / 4 : ℝ) := by
      have realPart : (parameter - cohomologicalPoint).re = parameter.re + 3 / 2 := by
        simp [cohomologicalPoint]
        ring
      calc
        |parameter.re + 3 / 2| = |(parameter - cohomologicalPoint).re| := by rw [realPart]
        _ ≤ ‖parameter - cohomologicalPoint‖ := Complex.abs_re_le_norm _
        _ < 1 / 4 := by simpa [dist_eq_norm] using distance
    rw [abs_lt] at absoluteBound
    constructor <;> linarith
  refine ⟨neighborhood, majorant, Metric.isOpen_ball,
    Metric.mem_ball_self (by norm_num), ?_, ?_, majorantIntegrable, ?_⟩
  · intro parameter
    exact (InducedContinuity.standardIntegrand_aestronglyMeasurable data extension parameter
      (flat.1 parameter) argument).restrict
  · intro coordinates parameter parameterMembership
    change DifferentiableWithinAt ℂ
      (fun value => extension value
        (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument))
      neighborhood parameter
    exact (flat.2.1 _ parameter).differentiableAt.differentiableWithinAt
  · intro coordinates parameter parameterMembership
    have intervalBounds := realBounds parameter parameterMembership
    simpa [majorant, standardIntegrand] using
      FlatNormStrip.flat_norm_strip_bound data extension flat
        (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument)
        (-7 / 4) (-5 / 4) parameter intervalBounds.1 intervalBounds.2

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardIntegrandDomination

end
