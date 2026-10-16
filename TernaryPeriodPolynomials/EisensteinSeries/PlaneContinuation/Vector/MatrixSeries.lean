module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.MatrixOrbit

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixSeries

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]
variable {Index : Type*}

theorem norm_summable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (index : Index → Rectangular ℚ) (injective : Function.Injective index) :
    Summable (fun i => ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i) binary‖) := by
  simpa only [term, norm_mul, Function.comp_def] using
    ((VectorTheta.summable_norm data family continuous realTest finiteTest finiteContinuous finiteSupport point binary).comp_injective injective).mul_left
      ‖GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)‖

theorem sum_norm_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (index : Index → Rectangular ℚ) (injective : Function.Injective index) (nonzero : ∀ i, index i ≠ 0) :
    (∑' i, ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i) binary‖) ≤
      ‖VectorAbsoluteTheta.function data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point binary‖ := by
  have bound : (∑' i, ‖VectorTheta.term data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary (index i)‖) ≤
      VectorAbsoluteTheta.base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary := by
    apply Summable.tsum_le_tsum_of_inj index injective (fun _ _ => norm_nonneg _) (fun i => ?_)
      ((VectorTheta.summable_norm data family continuous realTest finiteTest finiteContinuous finiteSupport point binary).comp_injective injective)
      (VectorAbsoluteTheta.summable data family continuous realTest finiteTest finiteContinuous finiteSupport point binary)
    rw [VectorAbsoluteTheta.tailTerm, ite_eq_right (nonzero i)]
    exact le_rfl
  rw [VectorAbsoluteTheta.function, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (VectorAbsoluteTheta.base_nonnegative _ _ _ _ _), mul_comm]
  simp only [term, norm_mul, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left bound (norm_nonneg _)

theorem sum_norm_integrable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (index : Index → Rectangular ℚ) (injective : Function.Injective index) (nonzero : ∀ i, index i ≠ 0) :
    IntegrableOn (fun binary => ∑' i, ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i) binary‖)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  let _ : Countable (Rectangular ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 2 → ℚ))
  let _ : Countable Index := injective.countable
  apply (VectorAbsoluteThetaDecay.integrable_domain data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).norm.mono'
  · exact (Measurable.tsum (fun i => (term_measurable data family continuous _
      (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) parameter point (index i)).norm)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun binary => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
      exact sum_norm_bound data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary index injective nonzero)

theorem term_integrable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (index : Index → Rectangular ℚ) (injective : Function.Injective index) (nonzero : ∀ i, index i ≠ 0) (i : Index) :
    IntegrableOn (term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i))
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  apply (sum_norm_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane index injective nonzero).mono'
    (term_measurable data family continuous _ (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) parameter point (index i)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun binary =>
    (norm_summable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary index injective).le_tsum i (fun _ _ => norm_nonneg _))

theorem integral_norm_summable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (index : Index → Rectangular ℚ) (injective : Function.Injective index) (nonzero : ∀ i, index i ≠ 0) :
    Summable (fun i => ∫ binary in BinaryFundamentalDomain.domain,
      ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i) binary‖ ∂BinaryHaar.measure) := by
  let _ : Countable (Rectangular ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 2 → ℚ))
  let _ : Countable Index := injective.countable
  let terms := fun i binary => ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i) binary‖
  have result := hasSum_integral_of_dominated_convergence (μ := BinaryHaar.measure.restrict BinaryFundamentalDomain.domain) terms
    (fun i => (term_measurable data family continuous _ (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous)
      parameter point (index i)).norm.aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall (fun binary => by
      change ‖‖term data family _ parameter point (index i) binary‖‖ ≤ _
      rw [norm_norm]))
    (Filter.Eventually.of_forall (fun binary => norm_summable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary index injective))
    (sum_norm_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane index injective nonzero)
    (Filter.Eventually.of_forall (fun binary => (norm_summable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary index injective).hasSum))
  exact result.summable

theorem hasSum_integral {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (index : Index → Rectangular ℚ) (injective : Function.Injective index) (nonzero : ∀ i, index i ≠ 0) :
    HasSum (fun i => ∫ binary in BinaryFundamentalDomain.domain,
      term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i) binary ∂BinaryHaar.measure)
      (∫ binary in BinaryFundamentalDomain.domain,
        ∑' i, term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i) binary ∂BinaryHaar.measure) := by
  let _ : Countable (Rectangular ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 2 → ℚ))
  let _ : Countable Index := injective.countable
  apply hasSum_integral_of_dominated_convergence (fun i binary =>
    ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i) binary‖)
  · exact fun i => (term_measurable data family continuous _
      (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) parameter point (index i)).aestronglyMeasurable
  · exact fun _ => Filter.Eventually.of_forall (fun _ => le_rfl)
  · exact Filter.Eventually.of_forall (fun binary => norm_summable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary index injective)
  · exact sum_norm_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane index injective nonzero
  · exact Filter.Eventually.of_forall (fun binary =>
      (norm_summable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary index injective).of_norm.hasSum)

theorem sum_integrable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (index : Index → Rectangular ℚ) (injective : Function.Injective index) (nonzero : ∀ i, index i ≠ 0) :
    IntegrableOn (fun binary => ∑' i, term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (index i) binary)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  let _ : Countable (Rectangular ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 2 → ℚ))
  let _ : Countable Index := injective.countable
  apply (sum_norm_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane index injective nonzero).mono'
  · exact (Measurable.tsum (fun i => term_measurable data family continuous _
      (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) parameter point (index i))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun binary => norm_tsum_le_tsum_norm
      (norm_summable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary index injective))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixSeries
