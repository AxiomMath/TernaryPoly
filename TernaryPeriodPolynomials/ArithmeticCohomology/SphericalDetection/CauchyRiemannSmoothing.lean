module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CircularMeanConvolution

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance CauchyRiemannSmoothing_measurableSpaceCircle : MeasurableSpace Circle := borel Circle
local instance CauchyRiemannSmoothing_borelSpaceCircle : BorelSpace Circle := ⟨rfl⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def radialMeanCorrection (radius : ℝ) (derivative : ℂ → E) (center : ℂ) : E :=
  ∫ direction : ℂ, complexRadialBump radius direction • circularMeanCorrection derivative center direction

omit [CompleteSpace E] in
theorem radialMeanCorrection_contDiff {order : ℕ∞} (radius : ℝ) (positive : 0 < radius)
    (derivative : ℂ → E) (regular : ContDiff ℝ order derivative) :
    ContDiff ℝ order (radialMeanCorrection radius derivative) := by
  have kernel : ContDiff ℝ order (fun parameter : ℂ × ℂ =>
      complexRadialBump radius parameter.2 • circularMeanCorrection derivative parameter.1 parameter.2) :=
    ((complexRadialBump_contDiff radius).comp contDiff_snd).smul (circularMeanCorrection_contDiff derivative regular)
  have integral_regular := contDiffOn_integral_compact_support (measure := volume)
    (values := fun center direction => complexRadialBump radius direction • circularMeanCorrection derivative center direction)
    isOpen_univ (complexRadialBump_hasCompactSupport radius positive)
    (fun _ direction _ outside => by rw [image_eq_zero_of_notMem_tsupport outside, zero_smul]) kernel.contDiffOn
  exact contDiffOn_univ.mp integral_regular

theorem radial_cauchyRiemann_formula (radius : ℝ) (positive : 0 < radius)
    (function : ℂ → E) (regular : ContDiff ℝ 1 function) (derivative : ℂ → E) (center : ℂ)
    (equation : ∀ point : ℂ, ‖point - center‖ ≤ radius → antiholomorphicDerivative function point = derivative point) :
    (∫ direction : ℂ, complexRadialBump radius direction) • function center =
      (∫ direction : ℂ, complexRadialBump radius direction • function (center + direction)) -
        radialMeanCorrection radius derivative center := by
  let mean : ℂ → E := fun direction =>
    ∫ angle : Circle, function (center + direction * (angle : ℂ)) ∂binaryRotationMeasure
  have mean_integrable : Integrable (fun direction => complexRadialBump radius direction • mean direction) := by
    have integrable := (radial_mean_integrable radius positive function regular.continuous center).integral_prod_left
    simpa only [integral_smul, mean] using integrable
  have constant_integrable : Integrable (fun direction => complexRadialBump radius direction • function center) :=
    ((complexRadialBump_contDiff radius (order := 0)).continuous.integrable_of_hasCompactSupport
      (complexRadialBump_hasCompactSupport radius positive)).smul_const _
  have pointwise (direction : ℂ) :
      complexRadialBump radius direction • mean direction - complexRadialBump radius direction • function center =
        complexRadialBump radius direction • circularMeanCorrection derivative center direction := by
    by_cases zero : complexRadialBump radius direction = 0
    · rw [zero, zero_smul, zero_smul, zero_smul, sub_self]
    have small : ‖direction‖ < radius := by
      by_contra outside
      exact zero (complexRadialBump_eq_zero_of_le radius positive direction (le_of_not_gt outside))
    dsimp only [mean]
    rw [← smul_sub, circularMean_affine_sub_eq_integral function regular center direction]
    congr 1
    apply intervalIntegral.integral_congr
    intro radial radial_mem
    have radial_bounds : 0 ≤ radial ∧ radial ≤ 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] using radial_mem
    apply integral_congr_ae
    filter_upwards [] with angle
    congr 1
    apply equation
    rw [add_sub_cancel_left, norm_smul, norm_mul, Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_nonneg radial_bounds.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) radial_bounds.2).trans small.le
  have integrated :
      (∫ direction : ℂ, complexRadialBump radius direction • mean direction) -
        (∫ direction : ℂ, complexRadialBump radius direction) • function center = radialMeanCorrection radius derivative center := by
    rw [← integral_smul_const, ← integral_sub mean_integrable constant_integrable]
    exact integral_congr_ae (Filter.Eventually.of_forall pointwise)
  dsimp only [mean] at integrated
  rw [integral_radial_circularMean radius positive function regular.continuous center] at integrated
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp integrated).symm

theorem contDiff_of_contDiff_antiholomorphicDerivative (function : ℂ → E)
    (regular : ContDiff ℝ 1 function) (derivative_regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (antiholomorphicDerivative function)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) function := by
  let mass : ℝ := ∫ direction : ℂ, complexRadialBump 1 direction
  have mass_nonzero : mass ≠ 0 := ne_of_gt (complexRadialBump_integral_pos 1 (by norm_num))
  have smooth := (contDiff_const (c := mass⁻¹)).smul
    ((radialAverage_contDiff 1 (by norm_num) function regular.continuous).sub
      (radialMeanCorrection_contDiff 1 (by norm_num) (antiholomorphicDerivative function) derivative_regular))
  convert smooth using 1
  funext center
  have formula := radial_cauchyRiemann_formula 1 (by norm_num) function regular
    (antiholomorphicDerivative function) center (fun _ _ => rfl)
  change function center = mass⁻¹ • ((∫ direction : ℂ, complexRadialBump 1 direction • function (center + direction)) -
    radialMeanCorrection 1 (antiholomorphicDerivative function) center)
  rw [← formula]
  exact (inv_smul_smul₀ mass_nonzero (function center)).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
