module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearMatrixBounds
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section


open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

noncomputable def realSpecialTent (radius : ℝ) (matrix : RealSL3) : ℂ :=
  (max 0 (radius - ‖matrix.val - 1‖) : ℝ)

theorem realSpecialTent_continuous (radius : ℝ) : Continuous (realSpecialTent radius) := by
  unfold realSpecialTent
  exact Complex.continuous_ofReal.comp
    (continuous_const.max (continuous_const.sub ((continuous_subtype_val.sub continuous_const).norm)))

theorem realSpecialTent_compactSupport (radius : ℝ) : HasCompactSupport (realSpecialTent radius) := by
  apply HasCompactSupport.intro (realSpecialLinear_norm_ball_compact 1 radius)
  intro matrix outside
  have smaller : radius < ‖matrix.val - 1‖ := lt_of_not_ge outside
  simp only [realSpecialTent, max_eq_left (sub_nonpos.mpr smaller.le), Complex.ofReal_zero]

theorem realSpecialTent_integrable (radius : ℝ) : Integrable (realSpecialTent radius) realSpecialLinearHaar :=
  (realSpecialTent_continuous radius).integrable_of_hasCompactSupport (realSpecialTent_compactSupport radius)

theorem realSpecialTent_lipschitz (radius : ℝ) (first second : RealSL3) :
    ‖realSpecialTent radius first - realSpecialTent radius second‖ ≤ ‖first.val - second.val‖ := by
  change ‖((max 0 (radius - ‖first.val - 1‖) : ℝ) : ℂ) -
    ((max 0 (radius - ‖second.val - 1‖) : ℝ) : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    max_comm 0, max_comm 0]
  calc
    _ ≤ |(radius - ‖first.val - 1‖) - (radius - ‖second.val - 1‖)| := abs_max_sub_max_le_abs _ _ _
    _ = |‖second.val - 1‖ - ‖first.val - 1‖| := by congr 1; ring
    _ ≤ ‖(second.val - 1) - (first.val - 1)‖ := abs_norm_sub_norm_le _ _
    _ = ‖first.val - second.val‖ := by rw [sub_sub_sub_cancel_right, norm_sub_rev]

theorem realSpecialLinear_lipschitz_kernel_translation_bound
    {kernel : RealSL3 → ℂ} (support : HasCompactSupport kernel) {constant : ℝ}
    (constant_nonnegative : 0 ≤ constant)
    (lipschitz : ∀ first second, ‖kernel first - kernel second‖ ≤ constant * ‖first.val - second.val‖)
    {translations : Set RealSL3} (compact : IsCompact translations) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ translation ∈ translations,
      (∫ matrix, ‖kernel (translation * matrix) - kernel matrix‖ ∂realSpecialLinearHaar) ≤
        bound * ‖translation.val - 1‖ := by
  let container : Set RealSL3 := tsupport kernel ∪ (translations⁻¹ * tsupport kernel)
  have container_compact : IsCompact container := support.union (compact.inv.mul support)
  obtain ⟨matrixBound, matrix_nonnegative, matrix_bounded⟩ := realSpecialLinear_compact_matrix_bounds container_compact
  let measureBound : ℝ := (realSpecialLinearHaar container).toReal
  refine ⟨measureBound * (constant * 3 * matrixBound), by dsimp [measureBound]; positivity, ?_⟩
  intro translation member
  have vanishes (matrix : RealSL3) (outside : matrix ∉ container) :
      ‖kernel (translation * matrix) - kernel matrix‖ = 0 := by
    have matrix_zero : kernel matrix = 0 :=
      image_eq_zero_of_notMem_tsupport (fun supported => outside (Or.inl supported))
    have translated_zero : kernel (translation * matrix) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro supported
      apply outside
      exact Or.inr ⟨translation⁻¹, by simpa only [Set.mem_inv, inv_inv] using member,
        translation * matrix, supported, inv_mul_cancel_left _ _⟩
    rw [matrix_zero, translated_zero, sub_self, norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero vanishes]
  have estimate (matrix : RealSL3) (contained : matrix ∈ container) :
      ‖kernel (translation * matrix) - kernel matrix‖ ≤
        (constant * 3 * matrixBound) * ‖translation.val - 1‖ := by
    have identity : (translation * matrix).val - matrix.val = (translation.val - 1) * matrix.val := by
      simp only [SpecialLinearGroup.coe_mul, sub_mul, one_mul]
    calc
      _ ≤ constant * ‖(translation * matrix).val - matrix.val‖ := lipschitz _ _
      _ = constant * ‖(translation.val - 1) * matrix.val‖ := by rw [identity]
      _ ≤ constant * (3 * ‖translation.val - 1‖ * ‖matrix.val‖) :=
        mul_le_mul_of_nonneg_left (ternary_matrix_norm_mul_le _ _) constant_nonnegative
      _ ≤ constant * (3 * ‖translation.val - 1‖ * matrixBound) := by
        gcongr
        exact (matrix_bounded matrix contained).1
      _ = _ := by ring
  have finite : IsFiniteMeasure (realSpecialLinearHaar.restrict container) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact container_compact.measure_lt_top⟩
  have integral_bound := setIntegral_mono_of_nonneg (μ := realSpecialLinearHaar)
    (fun matrix (_ : matrix ∈ container) => norm_nonneg (kernel (translation * matrix) - kernel matrix))
    estimate (integrable_const ((constant * 3 * matrixBound) * ‖translation.val - 1‖))
  simpa only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, measureReal_def,
    mul_assoc, measureBound] using integral_bound

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
