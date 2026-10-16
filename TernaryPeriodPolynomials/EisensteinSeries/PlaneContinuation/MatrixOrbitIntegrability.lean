module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MatrixStabilizerDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixOrbitIntegrability

theorem term_measurable {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (continuousTest : Continuous test) (vector : data.cusp.smooth) (parameter : ℂ)
    (point : AdelicGL) (matrix : Rectangular ℚ) : Measurable (term data test vector parameter point matrix) := by
  have termContinuous : Continuous (fun binary : BinaryAdelicGL => matrixTerm test point binary matrix) :=
    continuousTest.comp (continuous_const.matrix_mul
      (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) Adeles)))
  exact (termContinuous.measurable.mul ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp
    WeightedAbsoluteTheta.determinant_continuous.measurable)).mul (CuspFunctionContinuity.continuous data.cusp vector).measurable

theorem orbit_summable (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    Summable (fun coset : BinaryRationalGL ⧸ stabilizer matrix =>
      ‖matrixTerm (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary (orbitMap matrix coset)‖) := by
  have result := (AbsoluteTheta.summable realTest finiteTest finiteContinuous finiteSupport point binary).comp_injective
    (orbitMap_injective matrix)
  simpa only [Function.comp_def, AbsoluteTheta.tailTerm, ite_eq_right (orbitMap_nonzero matrix nonzero _)] using result

theorem orbit_bound (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    (∑' coset : BinaryRationalGL ⧸ stabilizer matrix,
      ‖matrixTerm (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary (orbitMap matrix coset)‖) ≤
      AbsoluteTheta.tail (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary := by
  apply Summable.tsum_le_tsum_of_inj (orbitMap matrix) (orbitMap_injective matrix) (fun _ _ => norm_nonneg _)
    (fun coset => ?_) (orbit_summable realTest finiteTest finiteContinuous finiteSupport point binary matrix nonzero)
    (AbsoluteTheta.summable realTest finiteTest finiteContinuous finiteSupport point binary)
  rw [AbsoluteTheta.tailTerm, ite_eq_right (orbitMap_nonzero matrix nonzero coset)]

theorem norm_summable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    Summable (fun coset : BinaryRationalGL ⧸ stabilizer matrix =>
      ‖term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix (coset.out⁻¹ • binary)‖) := by
  simp only [term_translate]
  simpa only [orbitMap, term, SingularCuspidality.weightedMatrixTerm, norm_mul] using
    ((orbit_summable realTest finiteTest finiteContinuous finiteSupport point binary matrix nonzero).mul_right
      ‖GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)‖).mul_right ‖data.cusp.realize vector binary‖

theorem sum_norm_bound {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    (∑' coset : BinaryRationalGL ⧸ stabilizer matrix,
      ‖term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix (coset.out⁻¹ • binary)‖) ≤
      ‖WeightedAbsoluteTheta.function data vector (AdelicSchwartzTheta.tensorTest realTest finiteTest) parameter point binary‖ := by
  rw [WeightedAbsoluteTheta.function, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (WeightedAbsoluteTheta.base_nonnegative _ _ _ _ _)]
  simp only [term_translate]
  simp only [term, SingularCuspidality.weightedMatrixTerm, norm_mul,
    tsum_mul_right, WeightedAbsoluteTheta.base]
  calc
    _ ≤ (AbsoluteTheta.tail (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary *
        ‖GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)‖) * ‖data.cusp.realize vector binary‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (orbit_bound realTest finiteTest finiteContinuous finiteSupport point binary matrix nonzero) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem integrable_domain {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    IntegrableOn (term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix)
      (domain matrix) BinaryHaar.measure := by
  exact SubgroupFundamentalDomain.integrable_of_periodized_bound (stabilizer matrix) BinaryFundamentalDomain.domain
    BinaryHaar.measure _ (term_measurable data _ (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous)
      vector parameter point matrix) _
    (AbsoluteThetaIntegrability.integrable_domain data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).norm
    (fun binary => norm_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary matrix nonzero)
    (fun binary => sum_norm_bound data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary matrix nonzero)

theorem hasSum_integral {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    HasSum (fun coset : BinaryRationalGL ⧸ stabilizer matrix => ∫ binary in BinaryFundamentalDomain.domain,
      term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point (orbitMap matrix coset) binary ∂BinaryHaar.measure)
      (∫ binary in domain matrix,
        term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix binary ∂BinaryHaar.measure) := by
  simpa only [term_translate, orbitMap, domain] using
    SubgroupFundamentalDomain.hasSum_integral (stabilizer matrix) BinaryFundamentalDomain.domain
      BinaryFundamentalDomain.domain_measurable BinaryFundamentalDomain.domain_unique BinaryHaar.measure _
      (integrable_domain data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane matrix nonzero)

theorem integral_norm_summable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) :
    Summable (fun coset : BinaryRationalGL ⧸ stabilizer matrix => ∫ binary in BinaryFundamentalDomain.domain,
      ‖term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point (orbitMap matrix coset) binary‖ ∂BinaryHaar.measure) := by
  simpa only [term_translate, orbitMap] using
    SubgroupFundamentalDomain.norm_integral_summable (stabilizer matrix) BinaryFundamentalDomain.domain
      BinaryFundamentalDomain.domain_measurable BinaryFundamentalDomain.domain_unique BinaryHaar.measure _
      (integrable_domain data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane matrix nonzero)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixOrbitIntegrability
