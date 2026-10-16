module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Hilbert
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Flat
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.StandardAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.VectorStripIntegral

@[expose] public section


/-!
# Analytic properties of the local Hilbert standard integral

The local standard integral `localValue` is the integral over the local coordinates `(ℝ × ℚ₃)²` of
the plane cusp-lift vector. Its analytic properties are those of the global integral of
`HilbertStandard`, and the proofs are the same dominated-convergence arguments, with the single
analytic input a majorant of the integrand by an integrable function of the local coordinates.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- A majorant of the local standard integrand, uniform for the arguments in a set: an integrable
function `bound` of the local coordinates and a constant dominating the norm of the integrand. -/
structure LocalMajorant {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (arguments : Set AdelicGL) where
  constant : ℝ
  bound : LocalLine × LocalLine → ℝ
  integrable : Integrable bound localRadicalMeasure
  dominates : ∀ argument ∈ arguments, ∀ coordinates,
    ‖localIntegrand data parameter function induced argument coordinates‖ ≤
      constant * bound coordinates

/-- Majorants of the local standard integrand of a flat family at every real parameter above
`threshold`, uniform for the arguments in every compact set. -/
structure LocalHalfPlaneMajorant {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (threshold : ℝ) where
  majorant : ∀ real : ℝ, threshold < real → ∀ arguments : Set AdelicGL, IsCompact arguments →
    LocalMajorant data (real : ℂ) (extension (real : ℂ)) (flat.1 (real : ℂ)) arguments

theorem localIntegrand_aestronglyMeasurable {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) :
    AEStronglyMeasurable (localIntegrand data parameter function induced argument)
      localRadicalMeasure :=
  (localIntegrand_continuous data parameter function induced argument).aestronglyMeasurable

namespace LocalMajorant

variable {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
  {induced : IsInduced data .plane parameter function} {arguments : Set AdelicGL}

/-- The local standard integrand is integrable at every argument with a majorant. -/
theorem integrable_integrand (majorant : LocalMajorant data parameter function induced arguments)
    {argument : AdelicGL} (membership : argument ∈ arguments) :
    Integrable (localIntegrand data parameter function induced argument) localRadicalMeasure :=
  (majorant.integrable.const_mul majorant.constant).mono'
    (localIntegrand_aestronglyMeasurable data parameter function induced argument)
    (Eventually.of_forall (majorant.dominates argument membership))

/-- The norm of the local standard integral is bounded by the integral of the majorant. -/
theorem norm_localValue_le (majorant : LocalMajorant data parameter function induced arguments)
    {argument : AdelicGL} (membership : argument ∈ arguments) :
    ‖localValue data parameter function induced argument‖ ≤
      majorant.constant * ∫ coordinates, majorant.bound coordinates ∂localRadicalMeasure := by
  unfold localValue
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (majorant.integrable.const_mul majorant.constant)
    (Eventually.of_forall (majorant.dominates argument membership))

/-- The local standard integral is continuous in the argument on a set with a majorant. -/
theorem continuousOn_localValue (majorant : LocalMajorant data parameter function induced arguments) :
    ContinuousOn (localValue data parameter function induced) arguments := by
  change ContinuousOn (fun argument => ∫ coordinates,
    localIntegrand data parameter function induced argument coordinates ∂localRadicalMeasure)
    arguments
  refine continuousOn_of_dominated (bound := fun coordinates => majorant.constant *
    majorant.bound coordinates) ?_ ?_ ?_ ?_
  · intro argument _
    exact localIntegrand_aestronglyMeasurable data parameter function induced argument
  · intro argument membership
    exact Eventually.of_forall (majorant.dominates argument membership)
  · exact majorant.integrable.const_mul majorant.constant
  · refine Eventually.of_forall (fun coordinates => ?_)
    have continuous : Continuous (fun argument : AdelicGL =>
        localIntegrand data parameter function induced argument coordinates) :=
      (CuspLift.continuous data .plane parameter function induced).comp
        (continuous_const.mul continuous_id)
    exact continuous.continuousOn

end LocalMajorant

/-- The local standard integral is the Bochner integral of an integrable function when a majorant
exists. -/
theorem localValue_integrable {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (arguments : Set AdelicGL) (majorant : LocalMajorant data parameter function induced arguments)
    {argument : AdelicGL} (membership : argument ∈ arguments) :
    Integrable (localIntegrand data parameter function induced argument) localRadicalMeasure :=
  majorant.integrable_integrand membership

/-- Continuity of the local standard integral in the argument, from majorants on compact sets. -/
theorem localValue_continuous {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (majorant : ∀ arguments : Set AdelicGL, IsCompact arguments →
      LocalMajorant data parameter function induced arguments) :
    Continuous (localValue data parameter function induced) := by
  apply continuous_iff_continuousAt.mpr
  intro argument
  obtain ⟨arguments, compact, neighborhood⟩ :=
    WeaklyLocallyCompactSpace.exists_compact_mem_nhds argument
  exact ((majorant arguments compact).continuousOn_localValue).continuousAt neighborhood

end TernaryPeriodPolynomials.EdgeConvergence
