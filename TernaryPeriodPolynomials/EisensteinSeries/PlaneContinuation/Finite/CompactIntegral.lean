module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.CoefficientEvaluation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ModeConvolution

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAveraging TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteCompactIntegral

instance levelCompact : CompactSpace finiteCongruence := isCompact_iff_compactSpace.mp finiteCongruence_isCompact

def measure : Measure finiteCongruence := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts finiteCongruence)

instance measureProbability : IsProbabilityMeasure measure := ⟨Measure.haarMeasure_self⟩
instance measureLeftInvariant : measure.IsMulLeftInvariant := inferInstanceAs (Measure.haarMeasure _).IsMulLeftInvariant

theorem orbit_integrable (data : CuspidalRepresentation) (vector : data.H) :
    Integrable (fun element : finiteCongruence => data.π (atFinite element.val) vector) measure :=
  ((data.continuous vector).comp (FiniteHilbertConvolution.atFinite_continuous.comp continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_fixed (data : CuspidalRepresentation) (vector : data.H) :
    (∫ element : finiteCongruence, data.π (atFinite element.val) vector ∂measure) ∈
      fixedSubspace data finiteCongruence := by
  intro element
  change unitaryOperator data (atFinite element.val) (∫ other : finiteCongruence, data.π (atFinite other.val) vector ∂measure) = _
  rw [← (unitaryOperator data (atFinite element.val)).integral_comp_comm (orbit_integrable data vector)]
  have equality (other : finiteCongruence) :
      unitaryOperator data (atFinite element.val) (data.π (atFinite other.val) vector) =
        data.π (atFinite (element * other).val) vector := (action_mul data element.val other.val vector).symm
  simp_rw [equality]
  exact integral_mul_left_eq_self (μ := measure) (fun other : finiteCongruence => data.π (atFinite other.val) vector) element

theorem integral_inner (data : CuspidalRepresentation) (vector target : data.H)
    (fixed : target ∈ fixedSubspace data finiteCongruence) :
    inner ℂ target (∫ element : finiteCongruence, data.π (atFinite element.val) vector ∂measure) = inner ℂ target vector := by
  have term (element : finiteCongruence) :
      inner ℂ target (data.π (atFinite element.val) vector) = inner ℂ target vector := by
    let isometry : data.H →ₗᵢ[ℂ] data.H := ⟨data.π (atFinite element.val), data.unitary (atFinite element.val)⟩
    have preservation := isometry.inner_map_map target vector
    change inner ℂ (data.π (atFinite element.val) target) (data.π (atFinite element.val) vector) = _ at preservation
    rwa [fixed element] at preservation
  rw [← _root_.integral_inner (orbit_integrable data vector) target]
  simp only [term]
  simp

theorem projection_eq_integral (data : CuspidalRepresentation) (vector : data.H) :
    averagingOperator data finiteCongruence vector =
      ∫ element : finiteCongruence, data.π (atFinite element.val) vector ∂measure := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (integral_fixed data vector)
  intro target fixed
  apply inner_eq_zero_symm.mp
  rw [inner_sub_right, integral_inner data vector target fixed, sub_self]

theorem realize_average (data : CuspidalRepresentation) (vector : data.smooth) (point : BinaryAdelicGL) :
    data.realize (smoothAverage data finiteCongruence finiteCongruence_isCompact vector) point =
      ∫ element : finiteCongruence, data.realize vector (point * atFinite element.val) ∂measure := by
  let span : Submodule ℂ data.H := Submodule.span ℂ
    (Set.range (fun element : finiteCongruence => data.π (atFinite element.val) vector.val))
  let _ : FiniteDimensional ℂ span := FiniteDimensional.span_of_finite ℂ
    (smooth_orbit_finite data finiteCongruence finiteCongruence_isCompact vector)
  have smoothContained : span ≤ data.smooth := by
    apply Submodule.span_le.mpr
    rintro _ ⟨element, rfl⟩
    exact data.smooth_stable _ _ vector.property
  let inclusion : span →ₗ[ℂ] data.smooth := span.subtype.codRestrict data.smooth (fun value => smoothContained value.property)
  let evaluationLinear : span →ₗ[ℂ] ℂ := ((LinearMap.proj point).comp data.realize).comp inclusion
  let evaluation : span →L[ℂ] ℂ := ⟨evaluationLinear, evaluationLinear.continuous_of_finiteDimensional⟩
  let orbit : finiteCongruence → span := fun element =>
    ⟨data.π (atFinite element.val) vector.val, Submodule.subset_span ⟨element, rfl⟩⟩
  have orbitContinuous : Continuous orbit :=
    (((data.continuous vector.val).comp (FiniteHilbertConvolution.atFinite_continuous.comp continuous_subtype_val))).subtype_mk _
  have orbitIntegrable : Integrable orbit measure :=
    orbitContinuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have vectorEquality : smoothAverage data finiteCongruence finiteCongruence_isCompact vector = inclusion (∫ element, orbit element ∂measure) := by
    apply Subtype.ext
    change averagingOperator data finiteCongruence vector.val = span.subtypeL (∫ element, orbit element ∂measure)
    rw [projection_eq_integral, ← span.subtypeL.integral_comp_comm orbitIntegrable]
    rfl
  rw [vectorEquality]
  change evaluation (∫ element, orbit element ∂measure) = _
  rw [← evaluation.integral_comp_comm orbitIntegrable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro element
  exact data.equivariant _ vector point

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteCompactIntegral
