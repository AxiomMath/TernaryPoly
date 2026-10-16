module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.MatrixSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularOrbitPartition
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorSingularTheta

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem fiber_integral_sum_zero {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) (orbit : Orbit) :
    (∑' matrix : {matrix : RankOne // orbitClass matrix = orbit}, ∫ binary in BinaryFundamentalDomain.domain,
      term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix.val.val binary ∂BinaryHaar.measure) = 0 := by
  rw [← (fiberEquiv orbit).tsum_eq]
  simp only [fiberEquiv_val]
  rw [(VectorMatrixOrbit.hasSum_integral data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
    orbit.out.val orbit.out.property.1).tsum_eq]
  exact VectorMatrixOrbit.singular_integral_zero data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
    orbit.out.val orbit.out.property.1 orbit.out.property.2

theorem singular_integral_zero {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    (∫ binary in BinaryFundamentalDomain.domain,
      ∑' matrix : RankOne, term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix.val binary ∂BinaryHaar.measure) = 0 := by
  have fiberSum := (VectorMatrixSeries.hasSum_integral data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
    (Subtype.val : RankOne → Rectangular ℚ) Subtype.val_injective (fun matrix => matrix.property.1)).tsum_fiberwise orbitClass
  have vanishing : ∀ orbit : Orbit,
      (∑' matrix : ↑(orbitClass ⁻¹' {orbit}), ∫ binary in BinaryFundamentalDomain.domain,
        term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix.val.val binary ∂BinaryHaar.measure) = 0 :=
    fiber_integral_sum_zero data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
  simpa only [vanishing, tsum_zero] using fiberSum.tsum_eq.symm

theorem rank_decomposition (function : Rectangular ℚ → ℂ) (summable : Summable function) (zero : function 0 = 0) :
    (∑' matrix : Frame, function matrix.val) + (∑' matrix : RankOne, function matrix.val) = ∑' matrix, function matrix := by
  classical
  have equality : (∑' matrix : {matrix : Rectangular ℚ // ¬ FullRank matrix}, function matrix.val) =
      ∑' matrix : RankOne, function matrix.val := by
    have first : (∑' matrix : {matrix : Rectangular ℚ // ¬ FullRank matrix}, function matrix.val) =
        ∑' matrix : Rectangular ℚ, {matrix : Rectangular ℚ | ¬ FullRank matrix}.indicator function matrix :=
      tsum_subtype {matrix : Rectangular ℚ | ¬ FullRank matrix} function
    have second : (∑' matrix : RankOne, function matrix.val) =
        ∑' matrix : Rectangular ℚ, {matrix : Rectangular ℚ | matrix ≠ 0 ∧ ¬ FullRank matrix}.indicator function matrix :=
      tsum_subtype {matrix : Rectangular ℚ | matrix ≠ 0 ∧ ¬ FullRank matrix} function
    rw [first, second]
    apply tsum_congr
    intro matrix
    by_cases isZero : matrix = 0
    · subst matrix
      simp [Set.indicator, zero]
    · by_cases singular : ¬ FullRank matrix
      · simp [Set.indicator, isZero, singular]
      · simp [Set.indicator, isZero, singular]
  rw [← equality]
  exact summable.tsum_subtype_add_tsum_subtype_compl {matrix : Rectangular ℚ | FullRank matrix}

omit [CompleteSpace Source] in
theorem term_zero {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (zero : test 0 = 0) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    term data family test parameter point 0 binary = 0 := by
  simp [term, VectorTheta.term, BanachAdelicTheta.matrixTerm, Matrix.map_zero, zero, map_zero]

theorem integrand_decomposition {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (zero : realTest 0 = 0) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    VectorThetaIntegral.integrand data family (BanachAdelicTheta.tensorTest realTest finiteTest) point parameter binary =
      (∑' matrix : Frame, term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix.val binary) +
      (∑' matrix : RankOne, term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix.val binary) := by
  have tensorZero : BanachAdelicTheta.tensorTest realTest finiteTest 0 = 0 := by
    change finiteTest 0 • realTest 0 = 0
    rw [zero, smul_zero]
  have summable : Summable (fun matrix => term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix binary) :=
    (VectorMatrixSeries.norm_summable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point binary id Function.injective_id).of_norm
  rw [rank_decomposition _ summable (term_zero data family _ tensorZero parameter point binary)]
  simp only [term, tsum_mul_left, VectorThetaIntegral.integrand]
  rw [(VectorTheta.hasSum data family continuous realTest finiteTest finiteContinuous finiteSupport point binary).tsum_eq]

theorem integral_eq_frame {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (zero : realTest 0 = 0) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    (∫ binary in BinaryFundamentalDomain.domain,
      VectorThetaIntegral.integrand data family (BanachAdelicTheta.tensorTest realTest finiteTest) point parameter binary ∂BinaryHaar.measure) =
      ∫ binary in BinaryFundamentalDomain.domain,
        ∑' matrix : Frame, term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix.val binary ∂BinaryHaar.measure := by
  simp only [integrand_decomposition data family continuous realTest zero finiteTest finiteContinuous finiteSupport parameter point]
  rw [integral_add
    (VectorMatrixSeries.sum_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
      (Subtype.val : Frame → Rectangular ℚ) Subtype.val_injective GodementQuotientIntegrability.frame_nonzero)
    (VectorMatrixSeries.sum_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
      (Subtype.val : RankOne → Rectangular ℚ) Subtype.val_injective (fun matrix => matrix.property.1)),
    singular_integral_zero data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane, add_zero]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorSingularTheta
