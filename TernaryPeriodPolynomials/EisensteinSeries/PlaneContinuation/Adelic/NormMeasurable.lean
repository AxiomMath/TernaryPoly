module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AbsoluteTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicNormMeasurable

noncomputable instance ideleMeasurableSpace : MeasurableSpace Adelesˣ := borel Adelesˣ

instance ideleBorelSpace : BorelSpace Adelesˣ := ⟨rfl⟩

theorem preimage_measure_measurable :
    Measurable (fun scalar : Adelesˣ => adeleMeasure ((fun value : Adeles => scalar.val * value) ⁻¹' additiveDomain)) := by
  have measurable : Measurable (fun pair : Adelesˣ × Adeles =>
      additiveDomain.indicator (fun _ => (1 : ENNReal)) (pair.1.val * pair.2)) :=
    (measurable_const.indicator RationalAdditiveDomain.domain_measurable).comp
      ((Units.continuous_val.measurable.comp measurable_fst).mul measurable_snd)
  have result := measurable.lintegral_prod_right' (ν := adeleMeasure)
  convert result using 1
  funext scalar
  have equality : (fun value : Adeles => additiveDomain.indicator (fun _ => (1 : ENNReal)) (scalar.val * value)) =
      ((fun value : Adeles => scalar.val * value) ⁻¹' additiveDomain).indicator 1 := by
    funext value
    by_cases membership : scalar.val * value ∈ additiveDomain <;> simp [membership]
  rw [equality]
  exact (lintegral_indicator_one (RationalAdditiveDomain.domain_measurable.preimage
    (show Measurable (fun value : Adeles => scalar.val * value) from measurable_const.mul measurable_id))).symm

theorem norm_eq_inverse_measure (scalar : Adelesˣ) :
    (adeleNorm scalar : ℝ) = (adeleMeasure ((fun value : Adeles => scalar.val * value) ⁻¹' additiveDomain)).toReal⁻¹ := by
  have equality := addEquivAddHaarChar_smul_preimage adeleMeasure (ContinuousAddEquiv.mulLeft scalar) (X := additiveDomain)
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleMeasure_additiveDomain] at equality
  have realEquality := congrArg ENNReal.toReal equality
  change ENNReal.toReal ((adeleNorm scalar : ENNReal) *
    adeleMeasure ((fun value : Adeles => scalar.val * value) ⁻¹' additiveDomain)) = ENNReal.toReal 1 at realEquality
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] at realEquality
  exact eq_inv_of_mul_eq_one_left realEquality

theorem norm_measurable : Measurable (fun scalar : Adelesˣ => (adeleNorm scalar : ℝ)) := by
  have inverseMeasurable : Measurable (fun scalar : Adelesˣ =>
      (adeleMeasure ((fun value : Adeles => scalar.val * value) ⁻¹' additiveDomain)).toReal⁻¹) :=
    measurable_inv.comp preimage_measure_measurable.ennreal_toReal
  convert inverseMeasurable using 1
  exact funext norm_eq_inverse_measure

theorem normPower_measurable (parameter : ℂ) : Measurable (fun scalar : Adelesˣ => normPower scalar parameter) :=
  Complex.continuous_exp.measurable.comp (measurable_const.mul
    (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp norm_measurable)))

theorem innerCharacter_measurable {degree : ℕ} (data : InducingData degree) (parameter : ℂ) :
    Measurable (GodementIntegral.innerCharacter data parameter) :=
  data.chi.continuous.measurable.inv.mul (normPower_measurable _)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicNormMeasurable
