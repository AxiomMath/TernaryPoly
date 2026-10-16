module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Standard
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.RankOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealTranslations

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertStandardAlgebra

def liftLinear {degree : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (argument : AdelicGL) : SectionSpace.inducedSections data side parameter →ₗ[ℂ] data.cusp.smooth where
  toFun sectionValue := CuspLift.vector data side parameter sectionValue.val sectionValue.property argument
  map_add' first second := by
    apply data.cusp.injective
    funext binary
    simp only [map_add, Pi.add_apply]
    erw [CuspLift.realizes, CuspLift.realizes, CuspLift.realizes]
    exact mul_add _ _ _
  map_smul' scalar sectionValue := by
    apply data.cusp.injective
    funext binary
    simp only [map_smul, Pi.smul_apply]
    erw [CuspLift.realizes, CuspLift.realizes]
    change _ * (scalar * _) = scalar * (_ * _)
    ring

theorem integrand_add {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (first second : SectionSpace.inducedSections data .plane parameter)
    (argument : AdelicGL) (coordinates : Adeles × Adeles) :
    HilbertStandard.integrand data parameter (first + second).val (first + second).property argument coordinates =
      HilbertStandard.integrand data parameter first.val first.property argument coordinates +
        HilbertStandard.integrand data parameter second.val second.property argument coordinates :=
  congrArg Subtype.val ((liftLinear data .plane parameter _).map_add first second)

theorem integrand_smul {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (scalar : ℂ) (sectionValue : SectionSpace.inducedSections data .plane parameter)
    (argument : AdelicGL) (coordinates : Adeles × Adeles) :
    HilbertStandard.integrand data parameter (scalar • sectionValue).val
        (scalar • sectionValue).property argument coordinates =
      scalar • HilbertStandard.integrand data parameter sectionValue.val sectionValue.property argument coordinates :=
  congrArg Subtype.val ((liftLinear data .plane parameter _).map_smul scalar sectionValue)

def valueLinear {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    SectionSpace.inducedSections data .plane parameter →ₗ[ℂ] (AdelicGL → data.cusp.H) where
  toFun sectionValue := HilbertStandard.value data parameter sectionValue.val sectionValue.property
  map_add' first second := by
    funext argument
    unfold HilbertStandard.value
    simp_rw [integrand_add]
    exact integral_add
      (HilbertStandard.integrand_integrable data parameter first.val first.property halfPlane argument)
      (HilbertStandard.integrand_integrable data parameter second.val second.property halfPlane argument)
  map_smul' scalar sectionValue := by
    funext argument
    unfold HilbertStandard.value
    simp_rw [integrand_smul]
    exact integral_smul scalar _

theorem lift_right_real {degree : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (sectionValue : SectionSpace.inducedSections data side parameter) (real : RealGL3) (argument : AdelicGL) :
    liftLinear data side parameter argument
        (RealTranslations.sectionRightReal data side parameter real sectionValue) =
      liftLinear data side parameter (argument * atInfinity real) sectionValue := by
  apply data.cusp.injective
  funext binary
  simp only [liftLinear, LinearMap.coe_mk, AddHom.coe_mk]
  erw [CuspLift.realizes, CuspLift.realizes]
  change normPower _ _ * sectionValue.val ((binaryLevi side binary * argument) * atInfinity real) = _
  rw [mul_assoc]

theorem value_right_real {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (sectionValue : SectionSpace.inducedSections data .plane parameter) (real : RealGL3) (argument : AdelicGL) :
    valueLinear data parameter halfPlane
        (RealTranslations.sectionRightReal data .plane parameter real sectionValue) argument =
      valueLinear data parameter halfPlane sectionValue (argument * atInfinity real) := by
  change HilbertStandard.value _ _ _ _ _ = HilbertStandard.value _ _ _ _ _
  unfold HilbertStandard.value
  apply integral_congr_ae
  filter_upwards [] with coordinates
  have equality := congrArg Subtype.val (lift_right_real data .plane parameter sectionValue real
    (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument))
  simpa only [liftLinear, LinearMap.coe_mk, AddHom.coe_mk, HilbertStandard.integrand, mul_assoc] using equality

theorem radicalIntegral_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (unit : Adelesˣ) (function : Adeles × Adeles → E) :
    ((adeleNorm unit : ℝ) * (adeleNorm unit : ℝ)) •
        (∫ coordinates, function (unit.val * coordinates.1, unit.val * coordinates.2)
          ∂radicalMeasure) =
      ∫ coordinates, function coordinates ∂radicalMeasure := by
  let equivalence := (ContinuousAddEquiv.mulLeft unit).toHomeomorph.toMeasurableEquiv
  have scaled := congrArg (fun measure : Measure (Adeles × Adeles) =>
    ∫ coordinates, function coordinates ∂measure) (StandardRankOne.radicalMeasure_scale unit)
  rw [integral_smul_nnreal_measure] at scaled
  have mapped := integral_map_equiv (μ := radicalMeasure)
    (equivalence.prodCongr equivalence) function
  change (∫ coordinates, function coordinates ∂Measure.map
      (fun coordinates : Adeles × Adeles =>
        (unit.val * coordinates.1, unit.val * coordinates.2)) radicalMeasure) =
    ∫ coordinates, function (unit.val * coordinates.1, unit.val * coordinates.2)
      ∂radicalMeasure at mapped
  rw [mapped] at scaled
  exact scaled

theorem integrand_rankOne {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (unit : Adelesˣ) (argument : AdelicGL) (coordinates : Adeles × Adeles) :
    HilbertStandard.integrand data parameter function induced (lineLevi unit 1 * argument) coordinates =
      (data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) •
        HilbertStandard.integrand data parameter function induced argument
          (unit.inv * coordinates.1, unit.inv * coordinates.2) := by
  unfold HilbertStandard.integrand
  rw [mul_assoc (weyl⁻¹ : AdelicGL), ← mul_assoc (lineUnipotent _ _),
    StandardRankOne.lineUnipotent_rankOne]
  simp only [mul_assoc]
  rw [← mul_assoc (weyl⁻¹ : AdelicGL) (lineLevi unit 1)
    (lineUnipotent (unit.inv * coordinates.1) (unit.inv * coordinates.2) * argument),
    weyl_inverse_lineLevi]
  simp only [mul_assoc]
  exact congrArg Subtype.val (CuspLiftCovariance.vector_plane_rankOne data parameter function induced unit
    (weyl⁻¹ * (lineUnipotent (unit.inv * coordinates.1) (unit.inv * coordinates.2) * argument)))

theorem value_rankOne {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (unit : Adelesˣ) (argument : AdelicGL) :
    HilbertStandard.value data parameter function induced (lineLevi unit 1 * argument) =
      (data.chi.toMonoidHom unit * normPower unit (2 * inductionExponent .line parameter)) •
        HilbertStandard.value data parameter function induced argument := by
  unfold HilbertStandard.value
  simp_rw [integrand_rankOne]
  rw [integral_smul]
  have scaled := radicalIntegral_scale unit
    (fun coordinates => HilbertStandard.integrand data parameter function induced argument
      (unit.inv * coordinates.1, unit.inv * coordinates.2))
  simp only [← mul_assoc, unit.inv_val, one_mul] at scaled
  rw [← scaled, NormPower.rankOne_factor]
  change (_ : ℂ) • ((adeleNorm unit : ℝ) * (adeleNorm unit : ℝ)) • _ = _
  rw [← IsScalarTower.algebraMap_smul (R := ℝ) ℂ, smul_smul]
  congr 1
  simp only [Complex.coe_algebraMap, Complex.ofReal_mul, pow_two, mul_assoc]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertStandardAlgebra
