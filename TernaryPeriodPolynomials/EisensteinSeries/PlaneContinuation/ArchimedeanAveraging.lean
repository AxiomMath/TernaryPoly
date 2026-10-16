module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.StageTranslation
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation
open MeasureTheory
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArchimedeanAveraging

theorem weighted_orbit_integrable (data : CuspidalRepresentation) (vector : data.H)
    {compactSet : Set BinaryRealGL} (compactness : IsCompact compactSet)
    [MeasurableSpace compactSet] [OpensMeasurableSpace compactSet]
    (measure : Measure compactSet) [IsFiniteMeasure measure]
    (weight : compactSet → ℂ) (continuousWeight : Continuous weight) :
    Integrable (fun matrix : compactSet => weight matrix • data.π (atInfinity matrix.val) vector) measure := by
  have : CompactSpace compactSet := isCompact_iff_compactSpace.mp compactness
  have continuity : Continuous (fun matrix : compactSet => weight matrix • data.π (atInfinity matrix.val) vector) :=
    continuousWeight.smul (((data.continuous vector).comp atInfinity_continuous).comp continuous_subtype_val)
  exact continuity.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Compact parameter families can be integrated within one complete analytic stage. -/
theorem integrable_weighted_parameter_integral_mem {Parameter : Type}
    [TopologicalSpace Parameter] [CompactSpace Parameter] [MeasurableSpace Parameter] [OpensMeasurableSpace Parameter]
    (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactLevel : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (fixed : vector.val ∈ fixedSubspace data level)
    (matrices : Parameter → BinaryRealGL) (continuousMatrices : Continuous matrices)
    (measure : Measure Parameter) [IsFiniteMeasure measure]
    (weight : Parameter → ℂ) (integrableWeight : Integrable weight measure) :
    (∫ parameter, weight parameter • data.π (atInfinity (matrices parameter)) vector.val ∂measure) ∈ data.smooth ∧
    (∫ parameter, weight parameter • data.π (atInfinity (matrices parameter)) vector.val ∂measure) ∈ fixedSubspace data level := by
  obtain ⟨radius, positiveRadius, family, continuousFamily, familyValue⟩ :=
    exists_compactParameterStageFamily data level openness compactLevel vector fixed matrices continuousMatrices
  have familyIntegrability : Integrable family measure :=
    continuousFamily.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨bound, boundProperty⟩ := isCompact_univ.exists_bound_of_continuousOn continuousFamily.continuousOn
  have integrability : Integrable (fun matrix => weight matrix • family matrix) measure :=
    integrableWeight.smul_bdd bound familyIntegrability.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun matrix => boundProperty matrix (Set.mem_univ matrix)))
  let integralStage : analyticStage data level radius positiveRadius :=
    ∫ parameter, weight parameter • family parameter ∂measure
  have functionEquality :
      (fun parameter => stageHilbertMap data level radius positiveRadius (weight parameter • family parameter)) =
      (fun parameter => weight parameter • data.π (atInfinity (matrices parameter)) vector.val) := by
    funext parameter
    rw [map_smul, familyValue]
  have integralEquality :
      (∫ parameter, weight parameter • data.π (atInfinity (matrices parameter)) vector.val ∂measure) =
        stageHilbertMap data level radius positiveRadius integralStage := by
    calc
      _ = ∫ parameter,
          stageHilbertMap data level radius positiveRadius (weight parameter • family parameter) ∂measure :=
        congrArg (fun function : Parameter → data.H => ∫ parameter, function parameter ∂measure) functionEquality.symm
      _ = _ := (stageHilbertMap data level radius positiveRadius).integral_comp_comm integrability
  rw [integralEquality]
  exact ⟨stageHilbertMap_mem_smooth data level openness compactLevel radius positiveRadius integralStage,
    integralStage.property.1⟩

/-- Every integrable scalar kernel on a compact real set preserves the analytic smooth submodule. -/
theorem integrable_weighted_integral_mem (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactLevel : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (fixed : vector.val ∈ fixedSubspace data level)
    {compactSet : Set BinaryRealGL} (compactness : IsCompact compactSet)
    [MeasurableSpace compactSet] [OpensMeasurableSpace compactSet]
    (measure : Measure compactSet) [IsFiniteMeasure measure]
    (weight : compactSet → ℂ) (integrableWeight : Integrable weight measure) :
    (∫ matrix : compactSet, weight matrix • data.π (atInfinity matrix.val) vector.val ∂measure) ∈ data.smooth ∧
    (∫ matrix : compactSet, weight matrix • data.π (atInfinity matrix.val) vector.val ∂measure) ∈ fixedSubspace data level := by
  have : CompactSpace compactSet := isCompact_iff_compactSpace.mp compactness
  exact integrable_weighted_parameter_integral_mem data level openness compactLevel vector fixed
    Subtype.val continuous_subtype_val measure weight integrableWeight

theorem weighted_integral_mem (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactLevel : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (fixed : vector.val ∈ fixedSubspace data level)
    {compactSet : Set BinaryRealGL} (compactness : IsCompact compactSet)
    [MeasurableSpace compactSet] [OpensMeasurableSpace compactSet]
    (measure : Measure compactSet) [IsFiniteMeasure measure]
    (weight : compactSet → ℂ) (continuousWeight : Continuous weight) :
    (∫ matrix : compactSet, weight matrix • data.π (atInfinity matrix.val) vector.val ∂measure) ∈ data.smooth ∧
    (∫ matrix : compactSet, weight matrix • data.π (atInfinity matrix.val) vector.val ∂measure) ∈ fixedSubspace data level := by
  have : CompactSpace compactSet := isCompact_iff_compactSpace.mp compactness
  exact integrable_weighted_integral_mem data level openness compactLevel vector fixed compactness measure weight
    (continuousWeight.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

noncomputable def weightedAverage (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactLevel : IsCompact (level : Set BinaryFiniteGL))
    (vector : TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedSmooth data level)
    {compactSet : Set BinaryRealGL} (compactness : IsCompact compactSet)
    [MeasurableSpace compactSet] [OpensMeasurableSpace compactSet]
    (measure : Measure compactSet) [IsFiniteMeasure measure]
    (weight : compactSet → ℂ) (continuousWeight : Continuous weight) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedSmooth data level :=
  ⟨⟨∫ matrix : compactSet, weight matrix • data.π (atInfinity matrix.val) vector.val.val ∂measure,
    (weighted_integral_mem data level openness compactLevel vector.val vector.property compactness
      measure weight continuousWeight).1⟩,
    (weighted_integral_mem data level openness compactLevel vector.val vector.property compactness
      measure weight continuousWeight).2⟩

theorem weightedAverage_val (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactLevel : IsCompact (level : Set BinaryFiniteGL))
    (vector : TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.fixedSmooth data level)
    {compactSet : Set BinaryRealGL} (compactness : IsCompact compactSet)
    [MeasurableSpace compactSet] [OpensMeasurableSpace compactSet]
    (measure : Measure compactSet) [IsFiniteMeasure measure]
    (weight : compactSet → ℂ) (continuousWeight : Continuous weight) :
    (weightedAverage data level openness compactLevel vector compactness measure weight continuousWeight).val.val =
      ∫ matrix : compactSet, weight matrix • data.π (atInfinity matrix.val) vector.val.val ∂measure := rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArchimedeanAveraging
