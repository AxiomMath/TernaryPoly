module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.QuotientMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

@[expose] public section


open Matrix MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "domainMeasure" => realSpecialLinearHaar.restrict principalRealSpecialLinearDomain

theorem principalRealSpecialLinearDomain_integral_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (function : RealSL3 → E)
    (invariant : ∀ principal : principalRealSpecialLinear, ∀ matrix,
      function (principal.val * matrix) = function matrix) (shift : RealSL3) :
    (∫ matrix, function (matrix * shift) ∂domainMeasure) = ∫ matrix, function matrix ∂domainMeasure := by
  have embedding : MeasurableEmbedding (fun matrix : RealSL3 => matrix * shift) :=
    (Homeomorph.mulRight shift).measurableEmbedding
  exact (((realSpecialLinearHaar_right_measurePreserving shift).restrict_image_emb
    embedding principalRealSpecialLinearDomain).integral_comp embedding function).trans
      ((principalRealSpecialLinearDomain_right_fundamental shift).setIntegral_eq
        principalRealSpecialLinearDomain_fundamental invariant)

theorem principal_correlation_continuous_of_approximation
    {function : RealSL3 → ℂ} (measurable : Measurable function)
    (invariant : ∀ principal : principalRealSpecialLinear, ∀ matrix,
      function (principal.val * matrix) = function matrix)
    {bound : ℝ} (nonnegative : 0 ≤ bound) (bounded : ∀ matrix, ‖function matrix‖ ≤ bound)
    {approximation : ℕ → RealSL3 → ℂ} (continuous : ∀ n, Continuous (approximation n))
    (approximation_bounded : ∀ n matrix, ‖approximation n matrix‖ ≤ 2 * bound)
    (approximation_invariant : ∀ n (principal : principalRealSpecialLinear) matrix,
      approximation n (principal.val * matrix) = approximation n matrix)
    (converges : ∀ matrix, Tendsto (fun n => approximation n matrix) atTop (nhds (function matrix))) :
    Continuous (fun shift => ∫ matrix, function matrix * star (function (matrix * shift)) ∂domainMeasure) := by
  let error (n : ℕ) (matrix : RealSL3) : ℝ := ‖function matrix - approximation n matrix‖
  have error_bounded (n : ℕ) (matrix : RealSL3) : error n matrix ≤ 3 * bound := by
    exact (norm_sub_le _ _).trans ((add_le_add (bounded matrix) (approximation_bounded n matrix)).trans_eq (by ring))
  have error_measurable (n : ℕ) : Measurable (error n) := (measurable.sub (continuous n).measurable).norm
  have error_integrable (n : ℕ) (shift : RealSL3) : Integrable (fun matrix => error n (matrix * shift)) domainMeasure :=
    Integrable.of_bound ((error_measurable n).comp (continuous_id.mul continuous_const).measurable).aestronglyMeasurable
      (3 * bound) (Eventually.of_forall (fun matrix => by simpa only [error, Real.norm_eq_abs, abs_norm] using error_bounded n (matrix * shift)))
  have error_limit : Tendsto (fun n => ∫ matrix, error n matrix ∂domainMeasure) atTop (nhds 0) := by
    have limit := tendsto_integral_filter_of_dominated_convergence (μ := domainMeasure)
      (F := error) (f := fun _ => (0 : ℝ)) (fun _ => 3 * bound)
      (Eventually.of_forall (fun n => (error_measurable n).aestronglyMeasurable))
      (Eventually.of_forall (fun n => Eventually.of_forall (fun matrix => by
        simpa only [error, Real.norm_eq_abs, abs_norm] using error_bounded n matrix)))
      (integrable_const _) (Eventually.of_forall (fun matrix => by
        simpa [error] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => function matrix) atTop _).sub (converges matrix)).norm))
    simpa only [integral_zero] using limit
  have integrable_product {other : RealSL3 → ℂ} (other_measurable : Measurable other)
      {other_bound : ℝ} (other_bounded : ∀ matrix, ‖other matrix‖ ≤ other_bound) (shift : RealSL3) :
      Integrable (fun matrix => function matrix * star (other (matrix * shift))) domainMeasure := by
    apply Integrable.of_bound
      (measurable.aestronglyMeasurable.mul
        ((other_measurable.comp (continuous_id.mul continuous_const).measurable).aestronglyMeasurable.star))
      (bound * other_bound)
    exact Eventually.of_forall (fun matrix => by
      change ‖function matrix * star (other (matrix * shift))‖ ≤ _
      rw [norm_mul, norm_star]
      exact mul_le_mul (bounded _) (other_bounded _) (norm_nonneg _) nonnegative)
  let correlation (shift : RealSL3) : ℂ := ∫ matrix, function matrix * star (function (matrix * shift)) ∂domainMeasure
  let approximants (n : ℕ) (shift : RealSL3) : ℂ := ∫ matrix, function matrix * star (approximation n (matrix * shift)) ∂domainMeasure
  have continuous_approximants (n : ℕ) : Continuous (approximants n) := by
    apply continuous_of_dominated (bound := fun _ => bound * (2 * bound))
    · intro shift
      exact (integrable_product (continuous n).measurable (approximation_bounded n) shift).aestronglyMeasurable
    · intro shift
      exact Eventually.of_forall (fun matrix => by
        rw [norm_mul, norm_star]
        exact mul_le_mul (bounded _) (approximation_bounded n _) (norm_nonneg _) nonnegative)
    · exact integrable_const _
    · exact Eventually.of_forall (fun matrix => continuous_const.mul
        (((continuous n).comp (continuous_const.mul continuous_id)).star))
  have estimate (n : ℕ) (shift : RealSL3) :
      ‖correlation shift - approximants n shift‖ ≤ bound * ∫ matrix, error n matrix ∂domainMeasure := by
    dsimp only [correlation, approximants]
    rw [← integral_sub (integrable_product measurable bounded shift)
      (integrable_product (continuous n).measurable (approximation_bounded n) shift)]
    calc
      _ ≤ ∫ matrix, ‖function matrix * star (function (matrix * shift)) -
          function matrix * star (approximation n (matrix * shift))‖ ∂domainMeasure := norm_integral_le_integral_norm _
      _ ≤ ∫ matrix, bound * error n (matrix * shift) ∂domainMeasure := by
        apply integral_mono
          ((integrable_product measurable bounded shift).sub
            (integrable_product (continuous n).measurable (approximation_bounded n) shift)).norm
          ((error_integrable n shift).const_mul bound)
        intro matrix
        dsimp only [Pi.sub_apply]
        rw [← mul_sub, ← star_sub, norm_mul, norm_star]
        exact mul_le_mul_of_nonneg_right (bounded matrix) (norm_nonneg _)
      _ = bound * ∫ matrix, error n matrix ∂domainMeasure := by
        rw [integral_const_mul]
        congr 1
        apply principalRealSpecialLinearDomain_integral_right
        intro principal matrix
        simp only [error, invariant, approximation_invariant]
  have uniform : TendstoUniformly approximants correlation atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro epsilon positive
    have scaled_limit : Tendsto (fun n => bound * ∫ matrix, error n matrix ∂domainMeasure) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul error_limit
    have small : ∀ᶠ n in atTop, bound * ∫ matrix, error n matrix ∂domainMeasure < epsilon :=
      scaled_limit.eventually (gt_mem_nhds positive)
    filter_upwards [small] with n small_at
    intro shift
    rw [dist_eq_norm]
    exact (estimate n shift).trans_lt small_at
  exact uniform.continuous (Eventually.of_forall continuous_approximants).frequently

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
