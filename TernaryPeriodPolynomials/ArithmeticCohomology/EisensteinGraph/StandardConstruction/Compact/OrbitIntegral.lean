module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.OrbitRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.IntegralGluing

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactOrbitIntegral

def realizationGraph (data : CuspidalRepresentation) :
    Submodule ℂ (data.H × lp (fun _ : BinaryAdelicGL => ℂ) ⊤) :=
  LinearMap.range (data.smooth.subtype.prod (CuspSupNorm.boundedRealization data))

def stagePair {degree : ℕ} (data : InducingData degree)
    (radius : ℝ≥0) (positive : 0 < radius) :
    analyticStage data.cusp finiteCongruence radius positive →L[ℂ]
      data.cusp.H × lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  (stageHilbertMap data.cusp finiteCongruence radius positive).prod
    (CompactOrbitRealization.stageRealizationCLM data radius positive)

theorem stagePair_mem {degree : ℕ} (data : InducingData degree)
    (radius : ℝ≥0) (positive : 0 < radius)
    (element : analyticStage data.cusp finiteCongruence radius positive) :
    stagePair data radius positive element ∈ realizationGraph data.cusp :=
  ⟨(stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
    finiteCongruence_isCompact radius positive element).val, rfl⟩

def orbitPair {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (finite : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) (real : RealGL3) :
    data.cusp.H × lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  let vector := CuspLift.vector data .plane parameter function induced
    (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finite) * atInfinity real)
  (vector.val, CuspSupNorm.boundedRealization data.cusp vector)

theorem orbitPair_continuous {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (finite : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) :
    Continuous (orbitPair data parameter function induced finite) :=
  (CuspLift.real_continuous data .plane parameter function induced _).prodMk
    (CompactOrbitRealization.real_realization_continuous data parameter function induced finite)

theorem orbitPair_local_integral {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (finite : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (measure : Measure X) [IsFiniteMeasure measure]
    (realMap : X → RealGL3) (realContinuous : Continuous realMap) (center : X) :
    ∃ neighborhood : Set X, IsOpen neighborhood ∧ center ∈ neighborhood ∧
      ∀ subset, MeasurableSet subset → subset ⊆ neighborhood →
        (∫ point in subset, orbitPair data parameter function induced finite (realMap point)
          ∂measure) ∈ realizationGraph data.cusp := by
  classical
  obtain ⟨shiftRadius, positiveShift, radius, positive, lift, continuousLift, liftValue⟩ :=
    InducedAnalyticFamilies.exists_cuspVector_localStageFamily induced finite (realMap center)
  let offset : X → PlaneMatrix := fun point => (realMap point).val - (realMap center).val
  have offsetContinuous : Continuous offset :=
    (Units.continuous_val.comp realContinuous).sub continuous_const
  let neighborhood : Set X := {point | ‖offset point‖ < (shiftRadius : ℝ)}
  have neighborhoodOpen : IsOpen neighborhood :=
    isOpen_lt offsetContinuous.norm continuous_const
  have centerMember : center ∈ neighborhood := by
    change ‖(realMap center).val - (realMap center).val‖ < (shiftRadius : ℝ)
    simp only [sub_self, norm_zero]
    exact_mod_cast positiveShift
  refine ⟨neighborhood, neighborhoodOpen, centerMember, ?_⟩
  intro subset subsetMeasurable subsetIn
  let ball : Set X := {point | ‖offset point‖₊ ≤ shiftRadius}
  have ballClosed : IsClosed ball := isClosed_le offsetContinuous.nnnorm continuous_const
  let clipped : X → ParameterBall shiftRadius := fun point =>
    if membership : point ∈ ball then ⟨offset point, membership⟩ else ⟨0, by simp⟩
  have clippedMeasurable : Measurable clipped := by
    have insideContinuous : Continuous (fun point : ball =>
        (⟨offset point.val, point.property⟩ : ParameterBall shiftRadius)) :=
      (offsetContinuous.comp continuous_subtype_val).subtype_mk _
    exact Measurable.dite
      (f := fun point : ball => (⟨offset point.val, point.property⟩ : ParameterBall shiftRadius))
      (g := fun _ : ↑ballᶜ => (⟨0, by simp⟩ : ParameterBall shiftRadius))
      insideContinuous.measurable measurable_const ballClosed.measurableSet
  let mapped := Measure.map clipped (measure.restrict subset)
  let _ : CompactSpace (ParameterBall shiftRadius) :=
    isCompact_iff_compactSpace.mp
      (CompactOrbitRealization.parameterBall_compact shiftRadius)
  have liftIntegrable : Integrable lift mapped := by
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact (μ := mapped) isCompact_univ
        continuousLift.continuousOn)
  have pairIntegrable : Integrable (fun point => stagePair data radius positive (lift point))
      mapped := (stagePair data radius positive).integrable_comp liftIntegrable
  have localEquality : ∀ point ∈ subset,
      orbitPair data parameter function induced finite (realMap point) =
        stagePair data radius positive (lift (clipped point)) := by
    intro point member
    have inside : point ∈ ball := by
      have bound := subsetIn member
      exact_mod_cast (show ‖offset point‖ < (shiftRadius : ℝ) from bound).le
    have shift : (realMap center).val + (clipped point).val = (realMap point).val := by
      simp only [clipped, dite_eq_left inside, offset]
      abel
    have vectorEquality :
        (stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
          finiteCongruence_isCompact radius positive (lift (clipped point))).val =
        CuspLift.vector data .plane parameter function induced
          (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finite) *
            atInfinity (realMap point)) := by
      rw [CompactScalarRealization.cuspLift_eq_reference]
      apply Subtype.ext
      rw [show ((stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
          finiteCongruence_isCompact radius positive (lift (clipped point))).val).val =
          stageHilbertMap data.cusp finiteCongruence radius positive
            (lift (clipped point)) from rfl, liftValue, shift]
      simp only [InducedAnalyticFamilies.matrixCuspVector, invertibleMatrix_units]
    change (_, _) =
      (((stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
        finiteCongruence_isCompact radius positive (lift (clipped point))).val).val,
       CuspSupNorm.boundedRealization data.cusp
        (stageSmoothMap data.cusp finiteCongruence finiteCongruence_isOpen
          finiteCongruence_isCompact radius positive (lift (clipped point))).val)
    rw [vectorEquality]
  have integralEquality :
      (∫ point in subset, orbitPair data parameter function induced finite (realMap point)
        ∂measure) = stagePair data radius positive (∫ point, lift point ∂mapped) := by
    calc
      _ = ∫ point in subset, stagePair data radius positive (lift (clipped point)) ∂measure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem subsetMeasurable] with point member
        exact localEquality point member
      _ = ∫ point, stagePair data radius positive (lift point) ∂mapped :=
        (integral_map clippedMeasurable.aemeasurable pairIntegrable.aestronglyMeasurable).symm
      _ = _ := (stagePair data radius positive).integral_comp_comm liftIntegrable
  rw [integralEquality]
  exact stagePair_mem data radius positive _

theorem compact_orbit_integral {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (finite : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X] (measure : Measure X) [IsFiniteMeasure measure]
    (realMap : X → RealGL3) (realContinuous : Continuous realMap) :
    ∃ vector : data.cusp.smooth,
      vector.val = ∫ point, (CuspLift.vector data .plane parameter function induced
        (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finite) *
          atInfinity (realMap point))).val ∂measure ∧
      ∀ binary, data.cusp.realize vector binary =
        ∫ point, data.cusp.realize (CuspLift.vector data .plane parameter function induced
          (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finite) *
            atInfinity (realMap point))) binary ∂measure := by
  let pair := fun point => orbitPair data parameter function induced finite (realMap point)
  have continuousPair : Continuous pair :=
    (orbitPair_continuous data parameter function induced finite).comp realContinuous
  have integrablePair : Integrable pair measure := by
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact (μ := measure) isCompact_univ
        continuousPair.continuousOn)
  have member : (∫ point, pair point ∂measure) ∈ realizationGraph data.cusp :=
    CompactIntegralGluing.integral_mem_of_local measure pair integrablePair
      (realizationGraph data.cusp)
      (orbitPair_local_integral data parameter function induced finite measure realMap realContinuous)
  obtain ⟨vector, equality⟩ := member
  refine ⟨vector, ?_, ?_⟩
  · have first := congrArg Prod.fst equality
    exact first.trans
      ((ContinuousLinearMap.fst ℂ data.cusp.H
        (lp (fun _ : BinaryAdelicGL => ℂ) ⊤)).integral_comp_comm integrablePair).symm
  · intro binary
    let evaluation := (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ binary).comp
      (ContinuousLinearMap.snd ℂ data.cusp.H (lp (fun _ : BinaryAdelicGL => ℂ) ⊤))
    have value := congrArg (fun value => evaluation value) equality
    exact value.trans (evaluation.integral_comp_comm integrablePair).symm

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactOrbitIntegral
