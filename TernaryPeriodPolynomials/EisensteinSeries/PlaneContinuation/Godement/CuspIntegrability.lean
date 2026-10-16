module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.RawGodementBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.GodementRelations
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UnipotentCompactDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodementRelations
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentCompactDomain

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementCuspIntegrability

theorem kernel_eq {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (value : Adeles) (binary : BinaryAdelicGL) :
    cuspKernel data test parameter point (value, binary) =
      VectorGodement.integrand data test parameter (planeLevi (binaryUnipotent value) 1 * point) (binaryUnipotent value * binary) := by
  simp only [cuspKernel, VectorGodement.integrand, frame_levi_mul, inv_mul_cancel_left,
    map_mul, PlaneUnipotentCharts.binaryUnipotent_det, one_mul]

theorem norm_integral_eq {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (value : Adeles) :
    (∫ binary, ‖cuspKernel data test parameter point (value, binary)‖ ∂BinaryHaar.measure) =
      ∫ binary, ‖VectorGodement.integrand data test parameter (planeLevi (binaryUnipotent value) 1 * point) binary‖ ∂BinaryHaar.measure := by
  simp only [kernel_eq]
  exact integral_mul_left_eq_self (μ := BinaryHaar.measure)
    (fun binary => ‖VectorGodement.integrand data test parameter (planeLevi (binaryUnipotent value) 1 * point) binary‖)
    (binaryUnipotent value)

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]
variable {degree : ℕ} (data : InducingData degree)
variable (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
variable (continuous : Continuous (fun vector => (family vector).val.val))
variable (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
variable (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
variable (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re)

include continuous finiteContinuous

theorem measurable (point : AdelicGL) :
    Measurable (cuspKernel data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) parameter point) := by
  have argument : Continuous (fun pair : Adeles × BinaryAdelicGL =>
      (planeLevi (binaryUnipotent pair.1) 1 * point, binaryUnipotent pair.1 * pair.2)) :=
    ((PlaneChartContinuity.leviUnipotent_continuous.comp continuous_fst).mul continuous_const).prodMk
      ((UnipotentAveragingAction.unipotent_continuous.comp continuous_fst).mul continuous_snd)
  have result := (CompactRawGodementBounds.raw_joint_measurable data family continuous realTest finiteTest finiteContinuous parameter).comp argument.measurable
  convert result using 1
  funext pair
  exact kernel_eq data _ parameter point pair.1 pair.2

include finiteSupport halfPlane

theorem integrable (point : AdelicGL) :
    Integrable (cuspKernel data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) parameter point)
      ((adeleMeasure.restrict additiveDomain).prod BinaryHaar.measure) := by
  let _ : IsProbabilityMeasure (adeleMeasure.restrict additiveDomain) :=
    ⟨by rw [Measure.restrict_apply_univ, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleMeasure_additiveDomain]⟩
  let pointMap := fun value : Adeles => planeLevi (binaryUnipotent value) 1 * point
  have mapContinuous : Continuous pointMap := PlaneChartContinuity.leviUnipotent_continuous.mul continuous_const
  let points := pointMap '' closureBox
  have compact : IsCompact points := closureBox_compact.image mapContinuous
  have membership : ∀ᵐ value ∂adeleMeasure.restrict additiveDomain, pointMap value ∈ points := by
    filter_upwards [ae_restrict_mem RationalAdditiveDomain.domain_measurable] with value membership
    exact ⟨value, domain_subset membership, rfl⟩
  have productIntegrable := CompactRawGodementBounds.product_integrable data family continuous realTest finiteTest
    finiteContinuous finiteSupport parameter ((RawGodementIntegrability.halfPlane_iff degree parameter).mpr halfPlane)
    (adeleMeasure.restrict additiveDomain) pointMap mapContinuous.measurable points compact membership
  apply (integrable_prod_iff (measurable data family continuous realTest finiteTest finiteContinuous parameter point).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro value
    have translated := (VectorUnfolding.raw_integrable_at data family continuous realTest finiteTest finiteContinuous finiteSupport
      parameter (pointMap value) halfPlane).comp_mul_left (binaryUnipotent value)
    apply translated.congr
    exact Filter.Eventually.of_forall (fun binary => (kernel_eq data _ parameter point value binary).symm)
  · apply productIntegrable.integral_norm_prod_left.congr
    exact Filter.Eventually.of_forall (fun value => (norm_integral_eq data _ parameter point value).symm)

theorem relations :
    CuspidalSectionRelations.Relations (VectorGodement.sectionFunction data
      (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) parameter) :=
  VectorGodementRelations.relations data _ parameter
    (integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter halfPlane)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementCuspIntegrability
