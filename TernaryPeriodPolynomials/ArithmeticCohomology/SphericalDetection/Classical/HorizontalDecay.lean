module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CuspSValue

@[expose] public section


open GeneralEisenstein Matrix MeasureTheory Filter
open scoped Topology

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem classicalBinaryForm_coord_horizontal_bound {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (position : Fin (degree + 1)) :
    ∃ constant : ℝ, ∀ᶠ height : ℝ in atTop, ∀ horizontal ∈ Set.Icc (0 : ℝ) 1,
      ‖(binaryStandardBasis degree).coord position
        (classicalBinaryForm form degree ((horizontal : ℂ) + Complex.I * (height : ℂ)))‖ ≤
          constant * (height ^ (degree - position.val) * Real.exp (-(2 * Real.pi) * height)) := by
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  obtain ⟨constant, constant_positive, bound⟩ := (CuspFormClass.exp_decay_atImInfty form (by norm_num : (0 : ℝ) < 1) period).exists_pos
  obtain ⟨threshold, after⟩ := (UpperHalfPlane.atImInfty_mem _).mp bound.bound
  refine ⟨constant * (degree.choose position.val : ℝ) * 2 ^ (degree - position.val), ?_⟩
  filter_upwards [eventually_ge_atTop threshold, eventually_ge_atTop (1 : ℝ)] with height after_threshold after_one
  intro horizontal member
  have height_positive : 0 < height := lt_of_lt_of_le zero_lt_one after_one
  let point : UpperHalfPlane := ⟨(horizontal : ℂ) + Complex.I * (height : ℂ), by simpa using height_positive⟩
  have point_eq : UpperHalfPlane.ofComplex ((horizontal : ℂ) + Complex.I * (height : ℂ)) = point :=
    UpperHalfPlane.ofComplex_apply point
  have point_im : point.im = height := by simp [point]
  have form_bound : ‖form point‖ ≤ constant * Real.exp (-(2 * Real.pi) * height) := by
    simpa only [Set.mem_ofPred_eq, point_im, div_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_mul] using
      after point (by simpa only [point_im] using after_threshold)
  have point_norm : ‖(point : ℂ)‖ ≤ 2 * height := by
    calc
      _ ≤ ‖(horizontal : ℂ)‖ + ‖Complex.I * (height : ℂ)‖ := norm_add_le _ _
      _ = horizontal + height := by
        simp [abs_of_nonneg member.1, abs_of_pos height_positive]
      _ ≤ _ := by linarith [member.2]
  calc
    _ = ‖form point‖ * ((degree.choose position.val : ℝ) * ‖(point : ℂ)‖ ^ (degree - position.val)) := by
      simp only [classicalBinaryForm, map_smul, smul_eq_mul, binaryPointPower_standardCoord,
        point_eq, norm_mul, norm_pow, norm_neg, Complex.norm_natCast]
      rfl
    _ ≤ (constant * Real.exp (-(2 * Real.pi) * height)) *
        ((degree.choose position.val : ℝ) * (2 * height) ^ (degree - position.val)) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

theorem classicalBinaryForm_coord_horizontal_integral_tendsto {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (position : Fin (degree + 1)) :
    Tendsto (fun height : ℝ => ∫ horizontal : ℝ in 0..1,
      (binaryStandardBasis degree).coord position
        (classicalBinaryForm form degree ((horizontal : ℂ) + Complex.I * (height : ℂ)))) atTop (𝓝 0) := by
  obtain ⟨constant, bound⟩ := classicalBinaryForm_coord_horizontal_bound form degree position
  have decay : Tendsto (fun height : ℝ =>
      constant * (height ^ (degree - position.val) * Real.exp (-(2 * Real.pi) * height))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((degree - position.val : ℕ) : ℝ) (2 * Real.pi)
        (mul_pos (by norm_num) Real.pi_pos)).const_mul constant
  apply squeeze_zero_norm' _ decay
  filter_upwards [bound] with height estimate
  have result := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (fun horizontal member =>
    estimate horizontal (by simpa only [Set.uIcc_of_le zero_le_one] using
      (Set.uIoc_subset_uIcc member)))
  simpa using result

end TernaryPeriodPolynomials.SphericalDetection.Helpers
