module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.CompactOrbitIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactAdelicIntegral

def evaluationGraph (data : CuspidalRepresentation) (test : BinaryAdelicGL) :
    Submodule ℂ (data.H × ℂ) :=
  LinearMap.range (data.smooth.subtype.prod ((LinearMap.proj test).comp data.realize))

def evaluatedPair {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (test : BinaryAdelicGL)
    (argument : AdelicGL) : data.cusp.H × ℂ :=
  let vector := CuspLift.vector data .plane parameter function induced argument
  (vector.val, data.cusp.realize vector test)

theorem evaluatedPair_continuous {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (test : BinaryAdelicGL) :
    Continuous (evaluatedPair data parameter function induced test) := by
  apply (CuspLift.continuous data .plane parameter function induced).prodMk
  change Continuous (fun argument => data.cusp.realize
    (CuspLift.vector data .plane parameter function induced argument) test)
  simp only [CuspLift.realizes]
  exact continuous_const.mul ((InducedContinuity.induced_continuous data .plane
    parameter function induced).comp (continuous_const.mul continuous_id))

theorem evaluatedPair_integral_mem {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (test : BinaryAdelicGL)
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X] (measure : Measure X) [IsFiniteMeasure measure]
    (argumentMap : X → AdelicGL) (argumentContinuous : Continuous argumentMap) :
    (∫ point, evaluatedPair data parameter function induced test (argumentMap point)
      ∂measure) ∈ evaluationGraph data.cusp test := by
  let pair := fun point => evaluatedPair data parameter function induced test (argumentMap point)
  have pairContinuous : Continuous pair :=
    (evaluatedPair_continuous data parameter function induced test).comp argumentContinuous
  have pairIntegrable : Integrable pair measure := by
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact (μ := measure) isCompact_univ pairContinuous.continuousOn)
  apply CompactIntegralGluing.integral_mem_of_local measure pair pairIntegrable
    (evaluationGraph data.cusp test)
  intro center
  let reference := finiteGroup (argumentMap center)
  let neighborhood : Set X :=
    {point | reference⁻¹ * finiteGroup (argumentMap point) ∈ finiteLevel}
  have openness : IsOpen neighborhood :=
    FiniteLevelTopology.finiteLevel_isOpen.preimage
      (continuous_const.mul (InducedContinuity.finiteGroup_continuous.comp argumentContinuous))
  have centerMember : center ∈ neighborhood := by
    change (finiteGroup (argumentMap center))⁻¹ * finiteGroup (argumentMap center) ∈ finiteLevel
    simp
  refine ⟨neighborhood, openness, centerMember, ?_⟩
  intro subset subsetMeasurable subsetIn
  have equality : ∀ point ∈ subset,
      CuspLift.vector data .plane parameter function induced (argumentMap point) =
        CuspLift.vector data .plane parameter function induced
          (atFinite reference * atInfinity (realGroup (argumentMap point))) := by
    intro point member
    have split := InducedContinuity.split_right (argumentMap point) reference
    calc
      _ = CuspLift.vector data .plane parameter function induced
          (atFinite reference * atInfinity (realGroup (argumentMap point)) *
            atFinite (reference⁻¹ * finiteGroup (argumentMap point))) := congrArg _ split
      _ = _ := CuspLift.finite_invariant data .plane parameter function induced _
        ⟨_, subsetIn member⟩
  obtain ⟨vector, hilbert, scalar⟩ := AdelicCompactOrbitIntegral.compact_real_orbit_integral
    data parameter function induced (atFinite reference) (measure.restrict subset)
    (fun point => realGroup (argumentMap point))
    (InducedContinuity.realGroup_continuous.comp argumentContinuous)
  refine ⟨vector, ?_⟩
  apply Prod.ext
  · change vector.val = (∫ point in subset, pair point ∂measure).1
    refine hilbert.trans (Eq.trans ?_
      ((ContinuousLinearMap.fst ℂ data.cusp.H ℂ).integral_comp_comm
        (μ := measure.restrict subset) pairIntegrable.integrableOn))
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem subsetMeasurable] with point member
    exact (congrArg Subtype.val (equality point member)).symm
  · change data.cusp.realize vector test = (∫ point in subset, pair point ∂measure).2
    refine (scalar test).trans (Eq.trans ?_
      ((ContinuousLinearMap.snd ℂ data.cusp.H ℂ).integral_comp_comm
        (μ := measure.restrict subset) pairIntegrable.integrableOn))
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem subsetMeasurable] with point member
    exact congrArg (fun vector => data.cusp.realize vector test) (equality point member).symm

/-- Compact adelic integration commutes with the actual automorphic realization.
No continuity assumption on point evaluation in the Hilbert norm is used. -/
theorem compact_adelic_integral {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X] (measure : Measure X) [IsFiniteMeasure measure]
    (argumentMap : X → AdelicGL) (argumentContinuous : Continuous argumentMap) :
    ∃ vector : data.cusp.smooth,
      vector.val = ∫ point, (CuspLift.vector data .plane parameter function induced
        (argumentMap point)).val ∂measure ∧
      ∀ test, data.cusp.realize vector test =
        ∫ point, data.cusp.realize (CuspLift.vector data .plane parameter function induced
          (argumentMap point)) test ∂measure := by
  have coordinate (test : BinaryAdelicGL) : ∃ vector : data.cusp.smooth,
      vector.val = ∫ point, (CuspLift.vector data .plane parameter function induced
        (argumentMap point)).val ∂measure ∧
      data.cusp.realize vector test = ∫ point, data.cusp.realize
        (CuspLift.vector data .plane parameter function induced (argumentMap point)) test ∂measure := by
    obtain ⟨vector, equality⟩ := evaluatedPair_integral_mem data parameter function induced
      test measure argumentMap argumentContinuous
    have integrable : Integrable (fun point => evaluatedPair data parameter function induced
        test (argumentMap point)) measure := by
      exact integrableOn_univ.mp
        (ContinuousOn.integrableOn_compact (μ := measure) isCompact_univ
          (((evaluatedPair_continuous data parameter function induced test).comp
            argumentContinuous).continuousOn))
    refine ⟨vector, ?_, ?_⟩
    · exact (congrArg Prod.fst equality).trans
        ((ContinuousLinearMap.fst ℂ data.cusp.H ℂ).integral_comp_comm integrable).symm
    · exact (congrArg Prod.snd equality).trans
        ((ContinuousLinearMap.snd ℂ data.cusp.H ℂ).integral_comp_comm integrable).symm
  obtain ⟨vector, hilbert, _⟩ := coordinate 1
  refine ⟨vector, hilbert, ?_⟩
  intro test
  obtain ⟨other, sameHilbert, scalar⟩ := coordinate test
  have same : vector = other := Subtype.ext (hilbert.trans sameHilbert.symm)
  exact same ▸ scalar

theorem compact_set_integral {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (measure : Measure X) [IsFiniteMeasureOnCompacts measure]
    (compact subset : Set X) (compactness : IsCompact compact) (inclusion : subset ⊆ compact)
    (argumentMap : X → AdelicGL) (argumentContinuous : Continuous argumentMap) :
    ∃ vector : data.cusp.smooth,
      vector.val = ∫ point in subset, (CuspLift.vector data .plane parameter function induced
        (argumentMap point)).val ∂measure ∧
      ∀ test, data.cusp.realize vector test =
        ∫ point in subset, data.cusp.realize (CuspLift.vector data .plane parameter function induced
          (argumentMap point)) test ∂measure := by
  let _ : CompactSpace compact := isCompact_iff_compactSpace.mp compactness
  let restricted := measure.restrict subset
  let _ : IsFiniteMeasure restricted := ⟨by
    change (measure.restrict subset) Set.univ < ⊤
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact (measure_mono inclusion).trans_lt compactness.measure_lt_top⟩
  let pulled := Measure.comap (Subtype.val : compact → X) restricted
  let _ : IsFiniteMeasure pulled := ⟨by
    exact (Measure.comap_apply_le (Subtype.val : compact → X) restricted
      MeasurableSet.univ.nullMeasurableSet).trans_lt (measure_lt_top _ _)⟩
  obtain ⟨vector, hilbert, scalar⟩ := compact_adelic_integral data parameter function induced
    pulled (fun point : compact => argumentMap point.val)
    (argumentContinuous.comp continuous_subtype_val)
  have intersection : compact ∩ subset = subset := Set.inter_eq_right.mpr inclusion
  refine ⟨vector, ?_, ?_⟩
  · have integralEquality := integral_subtype_comap (μ := restricted)
      compactness.measurableSet (fun point : X =>
        (CuspLift.vector data .plane parameter function induced (argumentMap point)).val)
    dsimp only [restricted] at integralEquality
    rw [Measure.restrict_restrict compactness.measurableSet, intersection] at integralEquality
    exact hilbert.trans integralEquality
  · intro test
    have integralEquality := integral_subtype_comap (μ := restricted)
      compactness.measurableSet (fun point : X => data.cusp.realize
        (CuspLift.vector data .plane parameter function induced (argumentMap point)) test)
    dsimp only [restricted] at integralEquality
    rw [Measure.restrict_restrict compactness.measurableSet, intersection] at integralEquality
    exact (scalar test).trans integralEquality

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactAdelicIntegral
