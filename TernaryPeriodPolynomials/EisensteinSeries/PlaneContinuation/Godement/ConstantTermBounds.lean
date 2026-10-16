module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.CuspIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentCompactDomain

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementConstantTermBounds

theorem determinant_continuous : Continuous (GeneralLinearGroup.det (n := Fin 3) (R := Adeles)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (Units.continuous_val (M := Matrix (Fin 3) (Fin 3) Adeles)).matrix_det
  · simp only [← map_inv]
    exact ((Units.continuous_val (M := Matrix (Fin 3) (Fin 3) Adeles)).comp continuous_inv).matrix_det

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]
variable {degree : ℕ} (data : InducingData degree)
variable (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
variable (continuous : Continuous (fun vector => (family vector).val.val))
variable (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
variable (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
variable (parameter : ℂ) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)

abbrev sections : ℂ → AdelicGL → ℂ :=
  VectorGodement.sectionFunction data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))

omit [CompleteSpace Source] in
theorem norm_bound (point : AdelicGL) (flag : Flags .plane) :
    ‖eisensteinSummand (sections data family realTest finiteTest) parameter point flag‖ ≤
      ‖GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point)‖ *
        ∫ binary, ‖VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
          parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure := by
  change ‖GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det (rationalGroup flag.out⁻¹ * point)) * _‖ ≤ _
  rw [norm_mul, GodementUnfolding.outer_rational_left]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)

include continuous finiteContinuous

theorem section_measurable : Measurable (sections data family realTest finiteTest parameter) := by
  have outer : Measurable (GodementIntegral.outerCharacter data parameter) :=
    data.chi.continuous.measurable.mul (AdelicNormMeasurable.normPower_measurable _)
  exact (outer.comp determinant_continuous.measurable).mul
    ((CompactRawGodementBounds.raw_joint_measurable data family continuous realTest finiteTest finiteContinuous parameter).stronglyMeasurable.integral_prod_right'
      (ν := BinaryHaar.measure)).measurable

theorem term_measurable (point : AdelicGL) (flag : Flags .plane) :
    Measurable (PlaneConstantTerm.term (sections data family realTest finiteTest) parameter point flag) :=
  (section_measurable data family continuous realTest finiteTest finiteContinuous parameter).comp
    (continuous_const.mul (PlaneChartContinuity.planeUnipotent_continuous.mul continuous_const)).measurable

include finiteSupport halfPlane

theorem summable_norm (point : AdelicGL) :
    Summable (fun flag => ‖eisensteinSummand (sections data family realTest finiteTest) parameter point flag‖) :=
  ((VectorRawNormSeries.hasSum data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).summable.mul_left
    ‖GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point)‖).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_bound data family realTest finiteTest parameter point)

theorem sum_norm_bound (point : AdelicGL) :
    (∑' flag, ‖eisensteinSummand (sections data family realTest finiteTest) parameter point flag‖) ≤
      ‖GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point)‖ *
        ∑' flag : Flags .plane, ∫ binary,
          ‖VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
            parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure := by
  rw [← tsum_mul_left]
  exact (summable_norm data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane point).tsum_le_tsum
    (norm_bound data family realTest finiteTest parameter point)
    ((VectorRawNormSeries.hasSum data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).summable.mul_left _)

theorem unipotent_sum_bound (point : AdelicGL) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ pair ∈ closureBox ×ˢ closureBox,
      (∑' flag, ‖PlaneConstantTerm.term (sections data family realTest finiteTest) parameter point flag pair‖) ≤ bound := by
  let points := (fun pair : Adeles × Adeles => planeUnipotent pair.1 pair.2 * point) '' (closureBox ×ˢ closureBox)
  have compact : IsCompact points := (closureBox_compact.prod closureBox_compact).image
    (PlaneChartContinuity.planeUnipotent_continuous.mul continuous_const)
  obtain ⟨bound, nonnegative, bounded⟩ := CompactRawGodementBounds.sum_bound data family continuous realTest finiteTest
    finiteContinuous finiteSupport parameter halfPlane points compact
  refine ⟨‖GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point)‖ * bound,
    mul_nonneg (norm_nonneg _) nonnegative, ?_⟩
  intro pair membership
  have inequality := sum_norm_bound data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane
    (planeUnipotent pair.1 pair.2 * point)
  simp only [map_mul, GodementIntegral.det_planeUnipotent, one_mul] at inequality
  exact inequality.trans (mul_le_mul_of_nonneg_left (bounded _ ⟨pair, membership, rfl⟩) (norm_nonneg _))

theorem sum_norm_integrable (point : AdelicGL) :
    Integrable (fun pair => ∑' flag, ‖PlaneConstantTerm.term (sections data family realTest finiteTest) parameter point flag pair‖)
      parameterMeasure := by
  obtain ⟨bound, _, bounded⟩ := unipotent_sum_bound data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane point
  have measurable : Measurable (fun pair : Adeles × Adeles =>
      ∑' flag, ‖PlaneConstantTerm.term (sections data family realTest finiteTest) parameter point flag pair‖) :=
    Measurable.tsum (fun flag => (term_measurable data family continuous realTest finiteTest finiteContinuous parameter point flag).norm)
  apply (integrable_const (μ := parameterMeasure) bound).mono' measurable.aestronglyMeasurable
  filter_upwards [ae_mem_domain] with pair membership
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  exact bounded pair ⟨domain_subset membership.1, domain_subset membership.2⟩

theorem term_integrable (point : AdelicGL) (flag : Flags .plane) :
    Integrable (PlaneConstantTerm.term (sections data family realTest finiteTest) parameter point flag) parameterMeasure := by
  apply (sum_norm_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane point).mono'
    (term_measurable data family continuous realTest finiteTest finiteContinuous parameter point flag).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun pair =>
    (summable_norm data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane
      (planeUnipotent pair.1 pair.2 * point)).le_tsum flag (fun _ _ => norm_nonneg _))

theorem integral_norm_summable (point : AdelicGL) :
    Summable (fun flag => ∫ pair, ‖PlaneConstantTerm.term (sections data family realTest finiteTest) parameter point flag pair‖ ∂parameterMeasure) := by
  have result := hasSum_integral_of_dominated_convergence
    (μ := parameterMeasure)
    (fun flag pair => ‖PlaneConstantTerm.term (sections data family realTest finiteTest) parameter point flag pair‖)
    (fun flag => (term_measurable data family continuous realTest finiteTest finiteContinuous parameter point flag).norm.aestronglyMeasurable)
    (fun _ => Filter.Eventually.of_forall (fun _ => by rw [norm_norm]))
    (Filter.Eventually.of_forall (fun pair => summable_norm data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane
      (planeUnipotent pair.1 pair.2 * point)))
    (sum_norm_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane point)
    (Filter.Eventually.of_forall (fun pair =>
      (summable_norm data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane
        (planeUnipotent pair.1 pair.2 * point)).hasSum))
  exact result.summable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementConstantTermBounds
