module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Analytic

@[expose] public section


/-!
# Parameter dependence of the local Hilbert standard integral

For a flat family `extension` of plane sections the local standard integral depends holomorphically
on the spectral parameter, and jointly continuously on parameter and argument, wherever its
integrand has an integrable majorant. The proofs are those of `HilbertFlat.standard_analytic_halfPlane`
and `HilbertTruncation.standard_joint_continuousAt` for the global integral: the norm of the integrand
on a vertical strip is bounded by its values on the boundary lines (`HilbertFlat.norm_strip_bound`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The local integrand of a flat family is the plane cusp lift at the local standard argument. -/
theorem localIntegrand_eq_lift {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (parameter : ℂ)
    (argument : AdelicGL) (coordinates : LocalLine × LocalLine) :
    localIntegrand data parameter (extension parameter) (flat.1 parameter) argument coordinates =
      HilbertFlat.lift data extension flat parameter
        (weyl⁻¹ * localRadical coordinates * argument) :=
  rfl

/-- On a vertical strip the local integrand of a flat family is dominated by its values on the
boundary lines. -/
theorem localIntegrand_strip_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (argument : AdelicGL)
    (coordinates : LocalLine × LocalLine) (lower upper : ℝ) (parameter : ℂ)
    (lowerBound : lower ≤ parameter.re) (upperBound : parameter.re ≤ upper) :
    ‖localIntegrand data parameter (extension parameter) (flat.1 parameter) argument
        coordinates‖ ≤
      ‖localIntegrand data (lower : ℂ) (extension (lower : ℂ)) (flat.1 (lower : ℂ)) argument
          coordinates‖ +
        ‖localIntegrand data (upper : ℂ) (extension (upper : ℂ)) (flat.1 (upper : ℂ)) argument
          coordinates‖ :=
  HilbertFlat.norm_strip_bound data extension flat (weyl⁻¹ * localRadical coordinates * argument)
    lower upper parameter lowerBound upperBound

/-- Holomorphy of the local standard integral in the spectral parameter at the points of a
half plane on which the integrand is integrable at every real parameter. -/
theorem localValue_analyticAt_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (threshold : ℝ)
    (integrable : ∀ real : ℝ, threshold < real →
      Integrable (localIntegrand data (real : ℂ) (extension (real : ℂ)) (flat.1 (real : ℂ))
        argument) localRadicalMeasure)
    (parameter : ℂ) (halfPlane : threshold < parameter.re) :
    AnalyticAt ℂ (fun parameter =>
      localValue data parameter (extension parameter) (flat.1 parameter) argument) parameter := by
  let lower : ℝ := (threshold + parameter.re) / 2
  let upper : ℝ := parameter.re + 1
  have lowerHalfPlane : threshold < lower := by dsimp [lower]; linarith
  have upperHalfPlane : threshold < upper := by dsimp [upper]; linarith
  have differentiable := VectorStripIntegral.integral_differentiableOn_strip localRadicalMeasure
    (fun parameter => localIntegrand data parameter (extension parameter) (flat.1 parameter)
      argument)
    (fun parameter => localIntegrand_aestronglyMeasurable data parameter (extension parameter)
      (flat.1 parameter) argument)
    (fun coordinates parameter =>
      (HilbertFlat.analytic data extension flat (weyl⁻¹ * localRadical coordinates * argument)
        parameter).differentiableAt)
    lower upper
    (fun coordinates parameter lowerBound upperBound =>
      localIntegrand_strip_bound data extension flat argument coordinates lower upper parameter
        lowerBound upperBound)
    (integrable lower lowerHalfPlane) (integrable upper upperHalfPlane)
  apply differentiable.analyticAt
  apply ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
  constructor <;> dsimp [lower, upper] <;> linarith

/-- Holomorphy of the local standard integral in the spectral parameter on the half plane of a
majorant. -/
theorem localValue_analyticAt_of_majorant {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (threshold : ℝ)
    (majorant : LocalHalfPlaneMajorant data extension flat threshold)
    (argument : AdelicGL) (parameter : ℂ) (halfPlane : threshold < parameter.re) :
    AnalyticAt ℂ (fun parameter =>
      localValue data parameter (extension parameter) (flat.1 parameter) argument) parameter :=
  localValue_analyticAt_halfPlane data extension flat argument threshold
    (fun real above => (majorant.majorant real above {argument} isCompact_singleton).integrable_integrand
      (Set.mem_singleton argument))
    parameter halfPlane

/-- Joint continuity of the local standard integral in parameter and argument on a strip and a
compact set of arguments. -/
theorem localValue_continuousOn_strip {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (threshold : ℝ)
    (majorant : LocalHalfPlaneMajorant data extension flat threshold)
    (lower upper : ℝ) (lowerHalfPlane : threshold < lower) (upperHalfPlane : threshold < upper)
    (arguments : Set AdelicGL) (compact : IsCompact arguments) :
    ContinuousOn
      (fun pair : ℂ × AdelicGL =>
        localValue data pair.1 (extension pair.1) (flat.1 pair.1) pair.2)
      ({parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} ×ˢ arguments) := by
  let lowerMajorant := majorant.majorant lower lowerHalfPlane arguments compact
  let upperMajorant := majorant.majorant upper upperHalfPlane arguments compact
  change ContinuousOn (fun pair : ℂ × AdelicGL => ∫ coordinates,
    localIntegrand data pair.1 (extension pair.1) (flat.1 pair.1) pair.2 coordinates
      ∂localRadicalMeasure) _
  refine continuousOn_of_dominated
    (bound := fun coordinates => lowerMajorant.constant * lowerMajorant.bound coordinates +
      upperMajorant.constant * upperMajorant.bound coordinates) ?_ ?_ ?_ ?_
  · intro pair _
    exact localIntegrand_aestronglyMeasurable data pair.1 (extension pair.1) (flat.1 pair.1) pair.2
  · intro pair membership
    refine Eventually.of_forall (fun coordinates => ?_)
    exact (localIntegrand_strip_bound data extension flat pair.2 coordinates lower upper pair.1
      membership.1.1 membership.1.2).trans
        (add_le_add (lowerMajorant.dominates pair.2 membership.2 coordinates)
          (upperMajorant.dominates pair.2 membership.2 coordinates))
  · exact (lowerMajorant.integrable.const_mul _).add (upperMajorant.integrable.const_mul _)
  · refine Eventually.of_forall (fun coordinates => ?_)
    have continuous : Continuous (fun pair : ℂ × AdelicGL =>
        localIntegrand data pair.1 (extension pair.1) (flat.1 pair.1) pair.2 coordinates) :=
      (HilbertFlat.joint_continuous data extension flat).comp
        (continuous_fst.prodMk (continuous_const.mul continuous_snd))
    exact continuous.continuousOn

/-- Joint continuity of the local standard integral in parameter and argument on the half plane of
a majorant. -/
theorem localValue_jointContinuousAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (threshold : ℝ)
    (majorant : LocalHalfPlaneMajorant data extension flat threshold)
    (parameter : ℂ) (argument : AdelicGL) (halfPlane : threshold < parameter.re) :
    ContinuousAt
      (fun pair : ℂ × AdelicGL =>
        localValue data pair.1 (extension pair.1) (flat.1 pair.1) pair.2)
      (parameter, argument) := by
  let lower : ℝ := (threshold + parameter.re) / 2
  let upper : ℝ := parameter.re + 1
  have lowerHalfPlane : threshold < lower := by dsimp [lower]; linarith
  have upperHalfPlane : threshold < upper := by dsimp [upper]; linarith
  obtain ⟨arguments, compact, neighborhood⟩ :=
    WeaklyLocallyCompactSpace.exists_compact_mem_nhds argument
  apply (localValue_continuousOn_strip data extension flat threshold majorant lower upper
    lowerHalfPlane upperHalfPlane arguments compact).continuousAt
  apply prod_mem_nhds _ neighborhood
  apply Filter.mem_of_superset
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show lower < parameter.re ∧ parameter.re < upper by
          constructor <;> dsimp [lower, upper] <;> linarith))
  intro value membership
  exact ⟨membership.1.le, membership.2.le⟩

/-- Continuity of the local standard integral in the argument at a parameter of the half plane of a
majorant. -/
theorem localValue_continuous_argument {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (threshold : ℝ)
    (majorant : LocalHalfPlaneMajorant data extension flat threshold)
    (parameter : ℂ) (halfPlane : threshold < parameter.re) :
    Continuous (fun argument =>
      localValue data parameter (extension parameter) (flat.1 parameter) argument) := by
  apply continuous_iff_continuousAt.mpr
  intro argument
  exact ContinuousAt.comp'
    (f := fun argument : AdelicGL => (parameter, argument))
    (g := fun pair : ℂ × AdelicGL =>
      localValue data pair.1 (extension pair.1) (flat.1 pair.1) pair.2)
    (x := argument)
    (localValue_jointContinuousAt data extension flat threshold majorant parameter argument
      halfPlane) (continuous_const.prodMk continuous_id).continuousAt

end TernaryPeriodPolynomials.EdgeConvergence
