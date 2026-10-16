module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.OrbitPartition
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MatrixOrbitIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularOrbitPartition TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularMatrixSeries

/- Absolute convergence permits exchanging the singular sum and the quotient integral. -/

theorem zero_singular : ¬ FullRank (0 : Rectangular ℚ) := by
  simp [FullRank, exterior, crossProduct]

theorem remainder_eq_sum (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (summable : Summable (matrixTerm test point binary)) :
    singularTheta test point binary - test 0 = ∑' matrix : RankOne, matrixTerm test point binary matrix.val := by
  classical
  have singularSum : singularTheta test point binary =
      ∑' matrix : Rectangular ℚ, {matrix : Rectangular ℚ | ¬ FullRank matrix}.indicator (matrixTerm test point binary) matrix :=
    tsum_subtype {matrix : Rectangular ℚ | ¬ FullRank matrix} (matrixTerm test point binary)
  have rankOneSum : (∑' matrix : RankOne, matrixTerm test point binary matrix.val) =
      ∑' matrix : Rectangular ℚ, {matrix : Rectangular ℚ | matrix ≠ 0 ∧ ¬ FullRank matrix}.indicator (matrixTerm test point binary) matrix :=
    tsum_subtype {matrix : Rectangular ℚ | matrix ≠ 0 ∧ ¬ FullRank matrix} (matrixTerm test point binary)
  rw [singularSum, (summable.indicator {matrix | ¬ FullRank matrix}).tsum_eq_add_tsum_ite 0]
  rw [Set.indicator_of_mem zero_singular, NonzeroThetaIntegrability.zero_term, add_sub_cancel_left,
    rankOneSum]
  apply tsum_congr
  intro matrix
  by_cases zero : matrix = 0
  · simp [Set.indicator, zero]
  · by_cases singular : ¬ FullRank matrix
    · simp [Set.indicator, zero, singular]
    · simp [Set.indicator, zero, singular]

theorem norm_summable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (fun matrix : RankOne => ‖term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix.val binary‖) := by
  simpa only [term, SingularCuspidality.weightedMatrixTerm, norm_mul, Function.comp_def] using
    (((AdelicSchwartzTheta.summable_norm realTest finiteTest finiteContinuous finiteSupport point binary).subtype
      (fun matrix : Rectangular ℚ => matrix ≠ 0 ∧ ¬ FullRank matrix)).mul_right
      ‖GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)‖).mul_right ‖data.cusp.realize vector binary‖

theorem sum_norm_bound {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    (∑' matrix : RankOne, ‖term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix.val binary‖) ≤
      ‖WeightedAbsoluteTheta.function data vector (AdelicSchwartzTheta.tensorTest realTest finiteTest) parameter point binary‖ := by
  have bound : (∑' matrix : RankOne, ‖matrixTerm (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary matrix.val‖) ≤
      AbsoluteTheta.tail (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary := by
    apply Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective (fun _ _ => norm_nonneg _)
      (fun matrix => ?_)
      ((AdelicSchwartzTheta.summable_norm realTest finiteTest finiteContinuous finiteSupport point binary).subtype
        (fun matrix : Rectangular ℚ => matrix ≠ 0 ∧ ¬ FullRank matrix))
      (AbsoluteTheta.summable realTest finiteTest finiteContinuous finiteSupport point binary)
    rw [AbsoluteTheta.tailTerm, ite_eq_right matrix.property.1]
    exact le_rfl
  rw [WeightedAbsoluteTheta.function, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (WeightedAbsoluteTheta.base_nonnegative _ _ _ _ _)]
  simp only [term, SingularCuspidality.weightedMatrixTerm, norm_mul, tsum_mul_right, WeightedAbsoluteTheta.base]
  calc
    _ ≤ (AbsoluteTheta.tail (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary *
        ‖GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)‖) * ‖data.cusp.realize vector binary‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right bound (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem sum_norm_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    IntegrableOn (fun binary => ∑' matrix : RankOne,
      ‖term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix.val binary‖)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  apply (AbsoluteThetaIntegrability.integrable_domain data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).norm.mono'
  · exact (Measurable.tsum (fun matrix : RankOne => (MatrixOrbitIntegrability.term_measurable data _
      (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous) vector parameter point matrix.val).norm)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun binary => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
      exact sum_norm_bound data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary)

theorem weighted_sum {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (test : Rectangular Adeles → ℂ) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (summable : Summable (matrixTerm test point binary)) :
    (∑' matrix : RankOne, term data test vector parameter point matrix.val binary) =
      (singularTheta test point binary - test 0) * GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) *
        data.cusp.realize vector binary := by
  simp only [term, SingularCuspidality.weightedMatrixTerm, tsum_mul_right, remainder_eq_sum test point binary summable]

theorem hasSum_integral {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    HasSum (fun matrix : RankOne => ∫ binary in BinaryFundamentalDomain.domain,
      term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix.val binary ∂BinaryHaar.measure)
      (∫ binary in BinaryFundamentalDomain.domain,
        (singularTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary - AdelicSchwartzTheta.tensorTest realTest finiteTest 0) *
          GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary ∂BinaryHaar.measure) := by
  apply hasSum_integral_of_dominated_convergence (fun (matrix : RankOne) binary =>
    ‖term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix.val binary‖)
  · exact fun matrix => (MatrixOrbitIntegrability.term_measurable data _
      (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous) vector parameter point matrix.val).aestronglyMeasurable
  · exact fun _ => Filter.Eventually.of_forall (fun _ => le_rfl)
  · exact Filter.Eventually.of_forall (fun binary => norm_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary)
  · exact sum_norm_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
  · apply Filter.Eventually.of_forall
    intro binary
    rw [← weighted_sum data vector _ parameter point binary
      (AdelicSchwartzTheta.summable realTest finiteTest finiteContinuous finiteSupport point binary)]
    exact (norm_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary).of_norm.hasSum

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularMatrixSeries
