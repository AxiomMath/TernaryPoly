module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem adeleNorm_smul_map (idele : Adelesˣ) :
    adeleNorm idele • Measure.map (fun value : Adeles => idele.val * value) adeleMeasure = adeleMeasure :=
  addEquivAddHaarChar_smul_map adeleMeasure (ContinuousAddEquiv.mulLeft idele)

theorem radicalNorm_smul_map (idele : Adelesˣ) :
    (adeleNorm idele)^2 • Measure.map
      (fun coordinates : Adeles × Adeles => (idele.val * coordinates.1, idele.val * coordinates.2))
      radicalMeasure = radicalMeasure := by
  have measurable : Measurable (fun value : Adeles => idele.val * value) :=
    (continuous_const.mul continuous_id).measurable
  change (adeleNorm idele)^2 • Measure.map
    (Prod.map (fun value : Adeles => idele.val * value) (fun value : Adeles => idele.val * value))
      (adeleMeasure.prod adeleMeasure) = adeleMeasure.prod adeleMeasure
  rw [← Measure.map_prod_map _ _ measurable measurable]
  calc
    _ = (adeleNorm idele • Measure.map (fun value : Adeles => idele.val * value) adeleMeasure).prod
        (adeleNorm idele • Measure.map (fun value : Adeles => idele.val * value) adeleMeasure) := by
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, pow_two]
    _ = _ := by rw [adeleNorm_smul_map]

theorem radical_integral_inv_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : Adeles × Adeles → E) (idele : Adelesˣ) :
    (∫ coordinates : Adeles × Adeles,
      function (idele.inv * coordinates.1, idele.inv * coordinates.2) ∂radicalMeasure) =
        (adeleNorm idele)^2 • ∫ coordinates, function coordinates ∂radicalMeasure := by
  let equivalence : (Adeles × Adeles) ≃ᵐ (Adeles × Adeles) :=
    ((ContinuousAddEquiv.mulLeft idele).toHomeomorph.prodCongr
      (ContinuousAddEquiv.mulLeft idele).toHomeomorph).toMeasurableEquiv
  have scale : (adeleNorm idele)^2 • Measure.map equivalence radicalMeasure = radicalMeasure :=
    radicalNorm_smul_map idele
  calc
    _ = ∫ coordinates : Adeles × Adeles,
        function (idele.inv * coordinates.1, idele.inv * coordinates.2)
          ∂((adeleNorm idele)^2 • Measure.map equivalence radicalMeasure) := by rw [scale]
    _ = (adeleNorm idele)^2 • ∫ coordinates : Adeles × Adeles,
        function (idele.inv * coordinates.1, idele.inv * coordinates.2)
          ∂(Measure.map equivalence radicalMeasure) := integral_smul_nnreal_measure _ _
    _ = _ := by
      rw [integral_map_equiv]
      congr 1
      apply integral_congr_ae
      filter_upwards with coordinates
      change function (idele.inv * (idele.val * coordinates.1),
        idele.inv * (idele.val * coordinates.2)) = function coordinates
      simp only [← mul_assoc, idele.inv_val, one_mul]

theorem normPower_exponent_one (idele : Adelesˣ) :
    normPower idele 1 = ((adeleNorm idele : ℝ) : ℂ) := by
  have positive : 0 < (adeleNorm idele : ℝ) := NNReal.coe_pos.mpr (adeleNorm_pos idele)
  simp only [normPower, one_mul, ← Complex.ofReal_exp, Real.exp_log positive]

theorem normPower_exponent_two (idele : Adelesˣ) :
    normPower idele 2 = (((adeleNorm idele)^2 : NNReal) : ℂ) := by
  calc
    _ = normPower idele 1 * normPower idele 1 := by rw [← normPower_add]; norm_num
    _ = _ := by rw [normPower_exponent_one]; push_cast; ring

theorem radical_integral_inv_mul_complex (function : Adeles × Adeles → ℂ) (idele : Adelesˣ) :
    (∫ coordinates : Adeles × Adeles,
      function (idele.inv * coordinates.1, idele.inv * coordinates.2) ∂radicalMeasure) =
        normPower idele 2 * ∫ coordinates, function coordinates ∂radicalMeasure := by
  rw [radical_integral_inv_mul, normPower_exponent_two]
  rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
