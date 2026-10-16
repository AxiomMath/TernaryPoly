module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CauchyRiemannMeanRegularity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance CircularMeanConvolution_measurableSpaceCircle : MeasurableSpace Circle := borel Circle
local instance CircularMeanConvolution_borelSpaceCircle : BorelSpace Circle := ⟨rfl⟩

def circleMultiplicationIsometry (angle : Circle) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun point := (angle : ℂ) * point
  invFun point := ((angle⁻¹ : Circle) : ℂ) * point
  left_inv point := by
    change ((angle⁻¹ : Circle) : ℂ) * ((angle : ℂ) * point) = point
    rw [← mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]
  right_inv point := by
    change (angle : ℂ) * (((angle⁻¹ : Circle) : ℂ) * point) = point
    rw [← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul]
  map_add' _ _ := mul_add _ _ _
  map_smul' scalar point := by simp only [Complex.real_smul, RingHom.id_apply]; ring
  norm_map' point := by
    change ‖(angle : ℂ) * point‖ = ‖point‖
    rw [norm_mul, Circle.norm_coe, one_mul]

theorem integral_circle_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (angle : Circle) (function : ℂ → E) :
    (∫ point : ℂ, function ((angle : ℂ) * point)) = ∫ point : ℂ, function point :=
  (circleMultiplicationIsometry angle).measurePreserving.integral_comp
    (circleMultiplicationIsometry angle).toHomeomorph.measurableEmbedding function

def radialBumpBase : ContDiffBump (0 : ℝ) := ⟨1/4, 1, by norm_num, by norm_num⟩

def complexRadialBump (radius : ℝ) (point : ℂ) : ℝ :=
  radialBumpBase (Complex.normSq point / radius ^ 2)

theorem complexRadialBump_contDiff (radius : ℝ) {order : ℕ∞} : ContDiff ℝ order (complexRadialBump radius) := by
  unfold complexRadialBump
  apply radialBumpBase.contDiff.comp
  simp only [Complex.normSq_apply, div_eq_mul_inv]
  exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)).mul contDiff_const

theorem complexRadialBump_nonneg (radius : ℝ) (point : ℂ) : 0 ≤ complexRadialBump radius point :=
  radialBumpBase.nonneg

theorem complexRadialBump_zero (radius : ℝ) : complexRadialBump radius 0 = 1 := by
  apply radialBumpBase.one_of_mem_closedBall
  simp [radialBumpBase]

theorem complexRadialBump_rotation (radius : ℝ) (angle : Circle) (point : ℂ) :
    complexRadialBump radius ((angle : ℂ) * point) = complexRadialBump radius point := by
  simp only [complexRadialBump, map_mul, Circle.normSq_coe, one_mul]

theorem complexRadialBump_neg (radius : ℝ) (point : ℂ) : complexRadialBump radius (-point) = complexRadialBump radius point := by
  simp [complexRadialBump, Complex.normSq_apply]

theorem complexRadialBump_eq_zero_of_le (radius : ℝ) (positive : 0 < radius) (point : ℂ)
    (outside : radius ≤ ‖point‖) : complexRadialBump radius point = 0 := by
  apply radialBumpBase.zero_of_le_dist
  change (1 : ℝ) ≤ dist (Complex.normSq point / radius ^ 2) 0
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))]
  apply (le_div_iff₀ (sq_pos_of_pos positive)).mpr
  rw [one_mul, Complex.normSq_eq_norm_sq]
  nlinarith

theorem complexRadialBump_hasCompactSupport (radius : ℝ) (positive : 0 < radius) :
    HasCompactSupport (complexRadialBump radius) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) radius)
  intro point member
  change dist point 0 ≤ radius
  rw [dist_zero_right]
  by_contra outside
  exact member (complexRadialBump_eq_zero_of_le radius positive point (le_of_lt (lt_of_not_ge outside)))

theorem complexRadialBump_integral_pos (radius : ℝ) (positive : 0 < radius) :
    0 < ∫ point : ℂ, complexRadialBump radius point := by
  apply (complexRadialBump_contDiff radius (order := 0)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (complexRadialBump_hasCompactSupport radius positive) (complexRadialBump_nonneg radius)
  rw [complexRadialBump_zero]
  exact one_ne_zero

theorem radial_mean_integrable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (radius : ℝ) (positive : 0 < radius) (function : ℂ → E) (continuous : Continuous function) (center : ℂ) :
    Integrable (fun pair : ℂ × Circle => complexRadialBump radius pair.1 •
      function (center + pair.1 * (pair.2 : ℂ))) (volume.prod binaryRotationMeasure) := by
  have integrand : Continuous (fun pair : ℂ × Circle => complexRadialBump radius pair.1 •
      function (center + pair.1 * (pair.2 : ℂ))) :=
    ((complexRadialBump_contDiff radius (order := 0)).continuous.comp continuous_fst).smul
      (continuous.comp (by fun_prop))
  apply integrand.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    ((complexRadialBump_hasCompactSupport radius positive).prod isCompact_univ)
  intro pair member
  refine ⟨?_, Set.mem_univ _⟩
  by_contra outside
  apply member
  change complexRadialBump radius pair.1 • function (center + pair.1 * (pair.2 : ℂ)) = 0
  rw [image_eq_zero_of_notMem_tsupport outside, zero_smul]

theorem integral_radial_circularMean {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (radius : ℝ) (positive : 0 < radius) (function : ℂ → E) (continuous : Continuous function) (center : ℂ) :
    (∫ direction : ℂ, complexRadialBump radius direction •
      ∫ angle : Circle, function (center + direction * (angle : ℂ)) ∂binaryRotationMeasure) =
      ∫ direction : ℂ, complexRadialBump radius direction • function (center + direction) := by
  calc
    _ = ∫ direction : ℂ, ∫ angle : Circle,
        complexRadialBump radius direction • function (center + direction * (angle : ℂ)) ∂binaryRotationMeasure := by
      simp only [integral_smul]
    _ = ∫ angle : Circle, (∫ direction : ℂ,
        complexRadialBump radius direction • function (center + direction * (angle : ℂ))) ∂binaryRotationMeasure :=
      integral_integral_swap (radial_mean_integrable radius positive function continuous center)
    _ = ∫ _angle : Circle, (∫ direction : ℂ,
        complexRadialBump radius direction • function (center + direction)) ∂binaryRotationMeasure := by
      apply integral_congr_ae
      filter_upwards [] with angle
      have identity := integral_circle_mul angle (fun direction => complexRadialBump radius direction • function (center + direction))
      simp only [complexRadialBump_rotation] at identity
      simpa only [mul_comm] using identity
    _ = _ := by simp

theorem radialAverage_contDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (radius : ℝ) (positive : 0 < radius) (function : ℂ → E) (continuous : Continuous function) {order : ℕ∞} :
    ContDiff ℝ order (fun center : ℂ => ∫ direction : ℂ,
      complexRadialBump radius direction • function (center + direction)) := by
  have regular := (complexRadialBump_hasCompactSupport radius positive).contDiff_convolution_left
    (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) (complexRadialBump_contDiff radius (order := order)) continuous.locallyIntegrable
  convert regular using 1
  funext center
  have identity := integral_neg_eq_self (fun direction : ℂ =>
    complexRadialBump radius direction • function (center - direction)) volume
  simpa only [complexRadialBump_neg, sub_neg_eq_add, convolution, ContinuousLinearMap.lsmul_apply] using identity

end TernaryPeriodPolynomials.SphericalDetection.Helpers
