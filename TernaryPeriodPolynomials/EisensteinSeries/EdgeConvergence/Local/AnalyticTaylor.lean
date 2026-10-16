module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Analytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.TaylorBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RightOrbitAnalyticity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TaylorIntegral

@[expose] public section


/-!
# Real analyticity of the local Hilbert standard integral

The right orbit `x ↦ localValue (g · x)` under the real group is analytic when the Taylor
coefficients of the right orbit of the cusp lift at the points `w⁻¹ n(u) g` of the local integrand
have an integrable common majorant on a common ball. This is the local form of
`HilbertTaylorIntegral.value_expansion`: the coefficients are integrated term by term
(`TaylorIntegral.hasFPowerSeriesOnBall`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

open CompactTaylorBounds CuspTaylorBounds AdelicTaylorBounds

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  ContinuousMultilinearMap.normedSpace'

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    ContinuousENorm (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  SeminormedAddGroup.toContinuousENorm

local instance {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (order : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => Matrices) E) :=
  PseudoEMetricSpace.pseudoMetrizableSpace

/-- The Taylor series at the identity of the right orbit of the cusp lift at the local standard
argument with local coordinates `coordinates`. -/
def localIntegrandSeries {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (coordinates : LocalLine × LocalLine) :
    FormalMultilinearSeries ℝ Matrices data.cusp.H :=
  coefficients (matrixOrbit data .plane parameter function induced
    (weyl⁻¹ * localRadical coordinates * argument)) 1

theorem localIntegrandSeries_continuous {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (order : ℕ) :
    Continuous (fun coordinates =>
      localIntegrandSeries data parameter function induced argument coordinates order) :=
  (CuspTaylorBounds.coefficients_continuous data .plane parameter function induced order).comp
    ((continuous_const.mul localRadical_continuous).mul continuous_const)

/-- A common ball of convergence and an integrable majorant, geometric in the order, of the Taylor
coefficients of the right orbits of the cusp lift at the points of the local integrand. -/
structure LocalTaylorMajorant {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) where
  radius : ℝ≥0
  radius_pos : 0 < radius
  bound : LocalLine × LocalLine → ℝ
  integrable : Integrable bound localRadicalMeasure
  expansions : ∀ coordinates, HasFPowerSeriesOnBall
    (matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * argument))
    (localIntegrandSeries data parameter function induced argument coordinates) 1 radius
  dominates : ∀ coordinates order,
    ‖localIntegrandSeries data parameter function induced argument coordinates order‖ ≤
      bound coordinates * (radius : ℝ)⁻¹ ^ order

namespace LocalTaylorMajorant

variable {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
  {induced : IsInduced data .plane parameter function} {argument : AdelicGL}

/-- The Taylor coefficients of the local integrand are Bochner integrable, with a geometric bound
on their integral norms. -/
theorem coefficient_bounds (majorant : LocalTaylorMajorant data parameter function induced argument)
    (order : ℕ) :
    Integrable (fun coordinates =>
      localIntegrandSeries data parameter function induced argument coordinates order)
        localRadicalMeasure ∧
      (∫ coordinates, ‖localIntegrandSeries data parameter function induced argument
        coordinates order‖ ∂localRadicalMeasure) ≤
          (∫ coordinates, majorant.bound coordinates ∂localRadicalMeasure) *
            (majorant.radius : ℝ)⁻¹ ^ order := by
  have dominating : Integrable (fun coordinates =>
      majorant.bound coordinates * (majorant.radius : ℝ)⁻¹ ^ order) localRadicalMeasure :=
    majorant.integrable.mul_const _
  have integrable : Integrable (fun coordinates =>
      localIntegrandSeries data parameter function induced argument coordinates order)
        localRadicalMeasure :=
    dominating.mono' (localIntegrandSeries_continuous data parameter function induced argument
      order).aestronglyMeasurable (Eventually.of_forall (fun coordinates =>
        majorant.dominates coordinates order))
  refine ⟨integrable, ?_⟩
  calc
    _ ≤ ∫ coordinates, majorant.bound coordinates * (majorant.radius : ℝ)⁻¹ ^ order
          ∂localRadicalMeasure :=
      integral_mono integrable.norm dominating (fun coordinates =>
        majorant.dominates coordinates order)
    _ = _ := integral_mul_const _ _

/-- The local standard integral has a power series expansion along the right orbit of the real
group, obtained by integrating the Taylor coefficients of the integrand. -/
theorem localValue_expansion (majorant : LocalTaylorMajorant data parameter function induced argument) :
    HasFPowerSeriesOnBall (rightMatrix (localValue data parameter function induced) argument)
      (fun order => ∫ coordinates,
        localIntegrandSeries data parameter function induced argument coordinates order
          ∂localRadicalMeasure) 1 majorant.radius := by
  have expansion := TaylorIntegral.hasFPowerSeriesOnBall localRadicalMeasure
    (fun coordinates => matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * argument))
    (localIntegrandSeries data parameter function induced argument) 1 majorant.radius
    majorant.radius_pos (∫ coordinates, majorant.bound coordinates ∂localRadicalMeasure)
    majorant.expansions (fun order => (majorant.coefficient_bounds order).1)
    (fun order => (majorant.coefficient_bounds order).2)
  apply expansion.congr
  intro matrices _
  change (∫ coordinates, matrixOrbit data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * argument) matrices ∂localRadicalMeasure) =
    localValue data parameter function induced (argument * atInfinity (invertibleMatrix (matrices 0)))
  unfold localValue
  apply integral_congr_ae
  filter_upwards [] with coordinates
  simp only [CuspTaylorBounds.matrixOrbit, rightMatrix, SmoothJets.matrixExtension,
    localIntegrand, mul_assoc]

end LocalTaylorMajorant

/-- The right orbit of the local standard integral under the real group is analytic at the
identity. -/
theorem localValue_analyticAt_one {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL)
    (majorant : LocalTaylorMajorant data parameter function induced argument) :
    AnalyticAt ℝ (rightMatrix (localValue data parameter function induced) argument) 1 :=
  majorant.localValue_expansion.analyticAt

/-- The right orbit of the local standard integral under the real group is smooth, when the
Taylor majorants exist at every argument. -/
theorem localValue_right_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (majorant : ∀ argument, LocalTaylorMajorant data parameter function induced argument)
    (argument : AdelicGL) :
    Smooth (fun real : Fin 1 → RealGL3 =>
      localValue data parameter function induced (argument * atInfinity (real 0))) :=
  RightOrbitAnalyticity.smooth_of_analyticAt_one (localValue data parameter function induced)
    (fun argument => localValue_analyticAt_one data parameter function induced argument
      (majorant argument)) argument

end TernaryPeriodPolynomials.EdgeConvergence
