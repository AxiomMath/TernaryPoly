module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.JointContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.StripIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactParameterIntegral

theorem continuous_integralOn {X Y : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [WeaklyLocallyCompactSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (measure : Measure Y) (domain container : Set Y) [IsFiniteMeasure (measure.restrict domain)]
    (measurable : MeasurableSet domain) (contained : domain ⊆ container) (compact : IsCompact container)
    (function : X → Y → ℂ) (continuous : Continuous (Function.uncurry function)) :
    Continuous (fun parameter => ∫ argument in domain, function parameter argument ∂measure) := by
  apply continuous_iff_continuousAt.mpr
  intro parameter
  obtain ⟨set, setCompact, neighborhood⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds parameter
  obtain ⟨bound, bounded⟩ := (setCompact.prod compact).exists_bound_of_continuousOn continuous.continuousOn
  apply continuousAt_of_dominated (bound := fun _ : Y => bound)
  · exact Eventually.of_forall (fun parameter => (continuous.uncurry_left parameter).aestronglyMeasurable)
  · filter_upwards [neighborhood] with value membership
    filter_upwards [ae_restrict_mem measurable] with argument argumentMembership
    exact bounded (value, argument) ⟨membership, contained argumentMembership⟩
  · exact integrable_const bound
  · exact Eventually.of_forall (fun argument => (continuous.uncurry_right argument).continuousAt)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactParameterIntegral
