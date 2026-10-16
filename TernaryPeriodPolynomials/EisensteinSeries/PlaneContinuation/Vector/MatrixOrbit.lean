module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.AbsoluteThetaDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.SingularCancellation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

def liftTest {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) : Rectangular Adeles → data.cusp.smooth :=
  fun matrix => (family (test matrix)).val

def term {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (parameter : ℂ) (point : AdelicGL)
    (matrix : Rectangular ℚ) (binary : BinaryAdelicGL) : ℂ :=
  GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) *
    VectorTheta.term data family test point binary matrix

omit [CompleteSpace Source] in
theorem term_eq {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ) :
    term data family test parameter point matrix =
      VectorSingularCancellation.term data (liftTest data family test) parameter point matrix := rfl

omit [CompleteSpace Source] in
theorem term_translate {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ)
    (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    term data family test parameter point matrix (rational • binary) =
      term data family test parameter point (matrix * rational.val) binary :=
  VectorSingularCancellation.term_translate data (liftTest data family test) parameter point matrix rational binary

theorem term_measurable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (test : Rectangular Adeles → Source) (testContinuous : Continuous test)
    (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ) :
    Measurable (term data family test parameter point matrix) := by
  have termContinuous : Continuous (fun binary => VectorTheta.term data family test point binary matrix) :=
    (VectorTheta.term_continuous data family continuous test testContinuous matrix).comp
      (f := fun binary : BinaryAdelicGL => (point, binary)) (continuous_const.prodMk continuous_id)
  exact ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp
    WeightedAbsoluteTheta.determinant_continuous.measurable).mul termContinuous.measurable

theorem orbit_summable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    Summable (fun coset : BinaryRationalGL ⧸ stabilizer matrix =>
      ‖VectorTheta.term data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary (orbitMap matrix coset)‖) := by
  have result := (VectorAbsoluteTheta.summable data family continuous realTest finiteTest finiteContinuous finiteSupport point binary).comp_injective
    (orbitMap_injective matrix)
  simpa only [Function.comp_def, VectorAbsoluteTheta.tailTerm, ite_eq_right (orbitMap_nonzero matrix nonzero _)] using result

theorem orbit_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    (∑' coset : BinaryRationalGL ⧸ stabilizer matrix,
      ‖VectorTheta.term data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary (orbitMap matrix coset)‖) ≤
      VectorAbsoluteTheta.base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary := by
  apply Summable.tsum_le_tsum_of_inj (orbitMap matrix) (orbitMap_injective matrix) (fun _ _ => norm_nonneg _)
    (fun coset => ?_) (orbit_summable data family continuous realTest finiteTest finiteContinuous finiteSupport point binary matrix nonzero)
    (VectorAbsoluteTheta.summable data family continuous realTest finiteTest finiteContinuous finiteSupport point binary)
  rw [VectorAbsoluteTheta.tailTerm, ite_eq_right (orbitMap_nonzero matrix nonzero coset)]

theorem norm_summable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    Summable (fun coset : BinaryRationalGL ⧸ stabilizer matrix =>
      ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix (coset.out⁻¹ • binary)‖) := by
  simp only [term_translate]
  simpa only [orbitMap, term, norm_mul] using
    (orbit_summable data family continuous realTest finiteTest finiteContinuous finiteSupport point binary matrix nonzero).mul_left
      ‖GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)‖

theorem sum_norm_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    (∑' coset : BinaryRationalGL ⧸ stabilizer matrix,
      ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix (coset.out⁻¹ • binary)‖) ≤
      ‖VectorAbsoluteTheta.function data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point binary‖ := by
  rw [VectorAbsoluteTheta.function, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (VectorAbsoluteTheta.base_nonnegative _ _ _ _ _), mul_comm]
  simp only [term_translate]
  simp only [term, norm_mul, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left
    (orbit_bound data family continuous realTest finiteTest finiteContinuous finiteSupport point binary matrix nonzero) (norm_nonneg _)

theorem integrable_domain {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    IntegrableOn (term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix)
      (domain matrix) BinaryHaar.measure := by
  exact SubgroupFundamentalDomain.integrable_of_periodized_bound (stabilizer matrix) BinaryFundamentalDomain.domain
    BinaryHaar.measure _ (term_measurable data family continuous _ (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous)
      parameter point matrix) _
    (VectorAbsoluteThetaDecay.integrable_domain data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).norm
    (fun binary => norm_summable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary matrix nonzero)
    (fun binary => sum_norm_bound data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary matrix nonzero)

theorem hasSum_integral {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    HasSum (fun coset : BinaryRationalGL ⧸ stabilizer matrix => ∫ binary in BinaryFundamentalDomain.domain,
      term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (orbitMap matrix coset) binary ∂BinaryHaar.measure)
      (∫ binary in domain matrix,
        term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix binary ∂BinaryHaar.measure) := by
  simpa only [term_translate, orbitMap, domain] using
    SubgroupFundamentalDomain.hasSum_integral (stabilizer matrix) BinaryFundamentalDomain.domain
      BinaryFundamentalDomain.domain_measurable BinaryFundamentalDomain.domain_unique BinaryHaar.measure _
      (integrable_domain data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane matrix nonzero)

theorem integral_norm_summable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    Summable (fun coset : BinaryRationalGL ⧸ stabilizer matrix => ∫ binary in BinaryFundamentalDomain.domain,
      ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point (orbitMap matrix coset) binary‖ ∂BinaryHaar.measure) := by
  simpa only [term_translate, orbitMap] using
    SubgroupFundamentalDomain.norm_integral_summable (stabilizer matrix) BinaryFundamentalDomain.domain
      BinaryFundamentalDomain.domain_measurable BinaryFundamentalDomain.domain_unique BinaryHaar.measure _
      (integrable_domain data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane matrix nonzero)

theorem singular_integral_zero {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) (singular : ¬ FullRank matrix) :
    (∫ binary in domain matrix,
      term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix binary ∂BinaryHaar.measure) = 0 :=
  VectorSingularCancellation.integral_zero data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
    parameter point matrix nonzero singular
    (term_measurable data family continuous _ (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) parameter point matrix)
    (integrable_domain data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane matrix nonzero)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
