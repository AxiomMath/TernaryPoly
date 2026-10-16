module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.QuotientIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.NonzeroThetaIntegrability

theorem zero_term (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    matrixTerm test point binary 0 = test 0 := by
  simp [matrixTerm, Matrix.map_zero]

theorem remainder_eq_sum (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (summable : Summable (matrixTerm test point binary)) :
    fullTheta test point binary - test 0 = ∑' matrix, AbsoluteTheta.tailTerm test point binary matrix := by
  classical
  rw [fullTheta, summable.tsum_eq_add_tsum_ite 0, zero_term, add_sub_cancel_left]
  rfl

theorem remainder_bound (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) :
    ‖fullTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary -
      AdelicSchwartzTheta.tensorTest realTest finiteTest 0‖ ≤
        AbsoluteTheta.tail (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary := by
  rw [remainder_eq_sum _ point binary (AdelicSchwartzTheta.summable realTest finiteTest finiteContinuous finiteSupport point binary)]
  exact norm_tsum_le_tsum_norm (AbsoluteTheta.summable realTest finiteTest finiteContinuous finiteSupport point binary)

theorem nonzero_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    IntegrableOn (fun binary =>
      (fullTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary - AdelicSchwartzTheta.tensorTest realTest finiteTest 0) *
        innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  have thetaContinuous : Continuous (fun binary => fullTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary) :=
    (SchwartzThetaContinuity.fullTheta_continuous realTest finiteTest finiteContinuous finiteSupport).comp
    (f := fun binary : BinaryAdelicGL => (point, binary))
    (continuous_const.prodMk (continuous_id : Continuous (fun binary : BinaryAdelicGL => binary)))
  have measurable : Measurable (fun binary =>
      (fullTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary - AdelicSchwartzTheta.tensorTest realTest finiteTest 0) *
        innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary) :=
    ((thetaContinuous.sub continuous_const).measurable.mul
    ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp WeightedAbsoluteTheta.determinant_continuous.measurable)).mul
      (CuspFunctionContinuity.continuous data.cusp vector).measurable
  apply (AbsoluteThetaIntegrability.integrable_domain data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).norm.mono'
    measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro binary
  simp only [WeightedAbsoluteTheta.function, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (WeightedAbsoluteTheta.base_nonnegative _ _ _ _ _)]
  simp only [WeightedAbsoluteTheta.base]
  calc
    _ ≤ (AbsoluteTheta.tail (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary *
        ‖innerCharacter data parameter (GeneralLinearGroup.det binary)‖) * ‖data.cusp.realize vector binary‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (remainder_bound realTest finiteTest finiteContinuous finiteSupport point binary) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem frame_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    IntegrableOn (ThetaInvariance.integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  have measurable : Measurable (ThetaInvariance.integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point) := by
    have sumMeasurable : Measurable (fun binary => ∑' frame : Frame,
        weightedTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point frame binary) :=
      Measurable.tsum (fun frame => GodementQuotientIntegrability.term_measurable data _
      (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous) vector parameter point frame)
    convert sumMeasurable using 1
    exact funext (fun binary => integrand_eq_tsum data _ vector parameter point binary)
  apply (GodementQuotientIntegrability.sum_norm_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).mono'
    measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro binary
  rw [integrand_eq_tsum]
  exact norm_tsum_le_tsum_norm (GodementQuotientIntegrability.norm_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary)

theorem singular_nonzero_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    IntegrableOn (fun binary =>
      (singularTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary - AdelicSchwartzTheta.tensorTest realTest finiteTest 0) *
        innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  have result := (nonzero_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).sub
    (frame_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)
  convert result using 1
  funext binary
  simp only [Pi.sub_apply, ThetaInvariance.integrand]
  rw [AdelicSchwartzTheta.decomposition realTest finiteTest finiteContinuous finiteSupport point binary]
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.NonzeroThetaIntegrability
