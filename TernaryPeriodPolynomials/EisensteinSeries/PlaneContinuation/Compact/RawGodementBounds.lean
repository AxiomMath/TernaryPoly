module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.AbsoluteThetaBound
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.RawNormSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactRawGodementBounds

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]
variable {degree : ℕ} (data : InducingData degree)
variable (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
variable (continuous : Continuous (fun vector => (family vector).val.val))
variable (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
variable (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
variable (parameter : ℂ) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)

include continuous finiteContinuous finiteSupport halfPlane

theorem sum_bound (points : Set AdelicGL) (compact : IsCompact points) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ point ∈ points,
      (∑' flag : Flags .plane, ∫ binary,
        ‖VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
          parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure) ≤ bound := by
  obtain ⟨bound, integrable, bounds⟩ := CompactAbsoluteThetaBound.exists_bound data family continuous realTest finiteTest
    finiteContinuous finiteSupport parameter halfPlane points compact
  refine ⟨∫ binary in BinaryFundamentalDomain.domain, ‖bound binary‖ ∂BinaryHaar.measure,
    integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro point membership
  apply (VectorRawNormSeries.sum_bound data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).trans
  apply integral_mono
    (VectorAbsoluteThetaDecay.integrable_domain data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).norm
    integrable.norm
  intro binary
  exact (bounds point membership binary).trans (le_abs_self _)

theorem raw_bound (points : Set AdelicGL) (compact : IsCompact points) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ point ∈ points,
      (∫ binary, ‖VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
        parameter point binary‖ ∂BinaryHaar.measure) ≤ bound := by
  let flag : Flags .plane := QuotientGroup.mk 1
  let transformed := (fun point => rationalGroup flag.out * point) '' points
  have transformedCompact : IsCompact transformed := compact.image (continuous_const.mul continuous_id)
  obtain ⟨bound, nonnegative, bounds⟩ := sum_bound data family continuous realTest finiteTest finiteContinuous finiteSupport
    parameter halfPlane transformed transformedCompact
  refine ⟨bound, nonnegative, fun point membership => ?_⟩
  have sum := VectorRawNormSeries.hasSum data family continuous realTest finiteTest finiteContinuous finiteSupport
    parameter (rationalGroup flag.out * point) halfPlane
  have single := sum.summable.le_tsum flag (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))
  have result := single.trans (bounds _ ⟨point, membership, rfl⟩)
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] using result

omit finiteSupport halfPlane in
theorem raw_joint_measurable :
    Measurable (fun pair : AdelicGL × BinaryAdelicGL => VectorGodement.integrand data
      (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) parameter pair.1 pair.2) := by
  have measurable : Measurable (fun pair : AdelicGL × BinaryAdelicGL =>
      term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter pair.1 RectangularKernel.standard pair.2) :=
    (((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp
      WeightedAbsoluteTheta.determinant_continuous.measurable).comp measurable_snd).mul
      (VectorTheta.term_continuous data family continuous _
        (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) RectangularKernel.standard).measurable
  convert measurable using 1
  funext pair
  exact congrFun (VectorUnfolding.raw_eq_term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter pair.1) pair.2

omit finiteSupport halfPlane in
theorem raw_norm_measurable :
    Measurable (fun point => ∫ binary, ‖VectorGodement.integrand data
      (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) parameter point binary‖ ∂BinaryHaar.measure) :=
  ((raw_joint_measurable data family continuous realTest finiteTest finiteContinuous parameter).norm.stronglyMeasurable.integral_prod_right'
    (ν := BinaryHaar.measure)).measurable

theorem product_integrable {Space : Type*} [MeasurableSpace Space]
    (measure : Measure Space) [IsFiniteMeasure measure] (pointMap : Space → AdelicGL) (mapMeasurable : Measurable pointMap)
    (points : Set AdelicGL) (compact : IsCompact points) (membership : ∀ᵐ value ∂measure, pointMap value ∈ points) :
    Integrable (fun pair : Space × BinaryAdelicGL => VectorGodement.integrand data
      (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) parameter (pointMap pair.1) pair.2)
      (measure.prod BinaryHaar.measure) := by
  have joint := (raw_joint_measurable data family continuous realTest finiteTest finiteContinuous parameter).comp
    ((mapMeasurable.comp measurable_fst).prodMk measurable_snd)
  apply (integrable_prod_iff joint.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun value => VectorUnfolding.raw_integrable_at data family continuous realTest finiteTest
      finiteContinuous finiteSupport parameter (pointMap value) ((RawGodementIntegrability.halfPlane_iff degree parameter).mp halfPlane))
  · obtain ⟨bound, _, bounded⟩ := raw_bound data family continuous realTest finiteTest finiteContinuous finiteSupport
      parameter halfPlane points compact
    have measurable := (raw_norm_measurable data family continuous realTest finiteTest finiteContinuous parameter).comp mapMeasurable
    apply (integrable_const (μ := measure) bound).mono' measurable.aestronglyMeasurable
    filter_upwards [membership] with value valueMembership
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact bounded _ valueMembership

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactRawGodementBounds
