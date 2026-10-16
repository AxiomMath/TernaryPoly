module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AbsoluteThetaIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementQuotientIntegrability

theorem frame_nonzero (frame : Frame) : frame.val ≠ 0 := by
  intro zero
  apply frame.property
  simp [exterior, zero, crossProduct]

theorem tailTerm_frame (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) (frame : Frame) :
    AbsoluteTheta.tailTerm test point binary frame.val = term test point binary frame := by
  rw [AbsoluteTheta.tailTerm, ite_eq_right (frame_nonzero frame)]
  rfl

theorem frame_bound (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) :
    (∑' frame : Frame, ‖term (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary frame‖) ≤
      AbsoluteTheta.tail (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary := by
  exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective (fun _ _ => norm_nonneg _)
    (fun frame => le_of_eq (congrArg norm (tailTerm_frame _ point binary frame).symm))
    (AdelicSchwartzTheta.frame_summable_norm realTest finiteTest finiteContinuous finiteSupport point binary)
    (AbsoluteTheta.summable realTest finiteTest finiteContinuous finiteSupport point binary)

theorem term_measurable {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (continuousTest : Continuous test) (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (frame : Frame) :
    Measurable (weightedTerm data test vector parameter point frame) := by
  have termContinuous : Continuous (fun binary => term test point binary frame) := by
    simpa only [tailTerm_frame] using AbsoluteTheta.term_continuous test continuousTest point frame.val
  exact (termContinuous.measurable.mul ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp
    WeightedAbsoluteTheta.determinant_continuous.measurable)).mul (CuspFunctionContinuity.continuous data.cusp vector).measurable

theorem norm_summable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (fun frame => ‖weightedTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point frame binary‖) := by
  simpa only [weightedTerm, norm_mul] using
    ((AdelicSchwartzTheta.frame_summable_norm realTest finiteTest finiteContinuous finiteSupport point binary).mul_right
      ‖innerCharacter data parameter (GeneralLinearGroup.det binary)‖).mul_right ‖data.cusp.realize vector binary‖

theorem sum_norm_bound {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    (∑' frame, ‖weightedTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point frame binary‖) ≤
      ‖WeightedAbsoluteTheta.function data vector (AdelicSchwartzTheta.tensorTest realTest finiteTest) parameter point binary‖ := by
  rw [WeightedAbsoluteTheta.function, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (WeightedAbsoluteTheta.base_nonnegative _ _ _ _ _)]
  simp only [weightedTerm, norm_mul, tsum_mul_right, WeightedAbsoluteTheta.base]
  calc
    _ ≤ (AbsoluteTheta.tail (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary *
        ‖innerCharacter data parameter (GeneralLinearGroup.det binary)‖) * ‖data.cusp.realize vector binary‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (frame_bound realTest finiteTest finiteContinuous finiteSupport point binary) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem sum_norm_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    IntegrableOn (fun binary => ∑' frame,
      ‖weightedTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point frame binary‖)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  apply (AbsoluteThetaIntegrability.integrable_domain data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).norm.mono'
  · exact (Measurable.tsum (fun frame => (term_measurable data _
      (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous) vector parameter point frame).norm)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun binary => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
      exact sum_norm_bound data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary)

theorem term_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) (frame : Frame) :
    IntegrableOn (weightedTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point frame)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  apply (sum_norm_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).mono'
    (term_measurable data _ (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous)
      vector parameter point frame).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun binary =>
    (norm_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary).le_tsum frame (fun _ _ => norm_nonneg _))

theorem integral_norm_summable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    Summable (fun frame => ∫ binary in BinaryFundamentalDomain.domain,
      ‖weightedTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point frame binary‖ ∂BinaryHaar.measure) := by
  let terms := fun frame binary => ‖weightedTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point frame binary‖
  have result := hasSum_integral_of_dominated_convergence (μ := BinaryHaar.measure.restrict BinaryFundamentalDomain.domain) terms
    (fun frame => (term_measurable data _ (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous)
      vector parameter point frame).norm.aestronglyMeasurable)
    (fun frame => Filter.Eventually.of_forall (fun binary => by
      change ‖‖weightedTerm data _ vector parameter point frame binary‖‖ ≤ _
      rw [norm_norm]))
    (Filter.Eventually.of_forall (fun binary => norm_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary))
    (sum_norm_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)
    (Filter.Eventually.of_forall (fun binary => (norm_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary).hasSum))
  exact result.summable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementQuotientIntegrability
