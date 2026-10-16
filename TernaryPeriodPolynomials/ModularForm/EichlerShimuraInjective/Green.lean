module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.ArcSymmetry

@[expose] public section


/-!
# Green's formula on the truncated fundamental domain

`stokes_real`: for a `C¹` function `F` of `(x, y)` on `y > 0`, 1-periodic in `x`, with the arc symmetry, `∬_{F_T} (F_x - i F_y) = -i ∫ F(x, T) dx`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open scoped ComplexConjugate


/-- The data of a real-analytic Stokes configuration. -/
structure StokesData (F Fx Fy : ℝ → ℝ → ℂ) : Prop where
  dx : ∀ x y, 0 < y → HasDerivAt (fun t => F t y) (Fx x y) x
  dy : ∀ x y, 0 < y → HasDerivAt (fun t => F x t) (Fy x y) y
  cF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) {p | 0 < p.2}
  cFx : ContinuousOn (fun p : ℝ × ℝ => Fx p.1 p.2) {p | 0 < p.2}
  cFy : ContinuousOn (fun p : ℝ × ℝ => Fy p.1 p.2) {p | 0 < p.2}
  per : ∀ y, 0 < y → F (1 / 2) y = F (-1 / 2) y

namespace StokesData

variable {F Fx Fy : ℝ → ℝ → ℂ} (h : StokesData F Fx Fy)

include h

theorem continuous_x_F {y : ℝ} (hy : 0 < y) : Continuous (fun x => F x y) := by
  refine continuousOn_univ.mp ?_
  exact h.cF.comp (continuous_id.prodMk continuous_const).continuousOn (fun x _ => hy)

theorem continuous_x_Fx {y : ℝ} (hy : 0 < y) : Continuous (fun x => Fx x y) := by
  refine continuousOn_univ.mp ?_
  exact h.cFx.comp (continuous_id.prodMk continuous_const).continuousOn (fun x _ => hy)

theorem continuousOn_y_F {x a : ℝ} (ha : 0 < a) : ContinuousOn (fun y => F x y) (Ici a) :=
  h.cF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => lt_of_lt_of_le ha hy)

theorem continuousOn_y_Fy {x a : ℝ} (ha : 0 < a) : ContinuousOn (fun y => Fy x y) (Ici a) :=
  h.cFy.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => lt_of_lt_of_le ha hy)

theorem continuousOn_y_Fx {x a : ℝ} (ha : 0 < a) : ContinuousOn (fun y => Fx x y) (Ici a) :=
  h.cFx.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => lt_of_lt_of_le ha hy)

/-- FTC in `y`. -/
theorem integral_Fy {x a T : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    ∫ y in a..T, Fy x y = F x T - F x a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => ?_) ?_
  · have : 0 < y := by
      rw [uIcc_of_le haT] at hy; exact lt_of_lt_of_le ha hy.1
    exact h.dy x y this
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le haT]
    exact (h.continuousOn_y_Fy ha).mono (fun y hy => hy.1)

/-- FTC in `x`. -/
theorem integral_Fx {y a b : ℝ} (hy : 0 < y) (_hab : a ≤ b) :
    ∫ x in a..b, Fx x y = F b y - F a y := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => h.dx x y hy) ?_
  exact (h.continuous_x_Fx hy).intervalIntegrable _ _



theorem continuousOn_arcX_F {s : Set ℝ} (hs : ∀ y ∈ s, 0 < y) : ContinuousOn (fun y => F (arcX y) y) s :=
  h.cF.comp (arcX_continuous'.prodMk continuous_id).continuousOn (fun y hy => hs y hy)

theorem continuousOn_negarcX_F {s : Set ℝ} (hs : ∀ y ∈ s, 0 < y) : ContinuousOn (fun y => F (-arcX y) y) s :=
  h.cF.comp (arcX_continuous'.neg.prodMk continuous_id).continuousOn (fun y hy => hs y hy)

theorem subst_right :
    ∫ y in (Real.sqrt 3 / 2)..1, F (arcX y) y = ∫ x in (0 : ℝ)..(1 / 2), (x / arcY x) * F x (arcY x) := by
  have hmain := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := 1 / 2) (f := arcY)
    (f' := fun x => -x / arcY x) (g := fun y => F (arcX y) y)
    (fun x hx => by
      rw [uIcc_of_le (by norm_num)] at hx
      exact arcY_hasDerivAt (by rw [abs_of_nonneg hx.1]; linarith [hx.2]))
    (arcY_deriv_cont.mono (by rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by norm_num) le_rfl))
    (h.continuousOn_arcX_F (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hy
      rw [uIcc_of_le (by norm_num)] at hx
      exact arcY_pos (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)))
  rw [arcY_zero, arcY_half] at hmain
  have hcongr : ∫ x in (0 : ℝ)..(1 / 2), (-x / arcY x) • F (arcX (arcY x)) (arcY x) =
      ∫ x in (0 : ℝ)..(1 / 2), (-(x / arcY x)) * F x (arcY x) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le (by norm_num)] at hx
    rw [arcX_arcY_abs (by rw [abs_of_nonneg hx.1]; linarith [hx.2]), abs_of_nonneg hx.1,
      Complex.real_smul]
    push_cast
    ring
  simp only [Function.comp_apply] at hmain
  rw [hcongr] at hmain
  have hsym : ∫ y in (1 : ℝ)..(Real.sqrt 3 / 2), F (arcX y) y =
      -∫ y in (Real.sqrt 3 / 2)..1, F (arcX y) y := intervalIntegral.integral_symm _ _
  have : ∫ x in (0 : ℝ)..(1 / 2), (-(x / arcY x)) * F x (arcY x) =
      -∫ x in (0 : ℝ)..(1 / 2), (x / arcY x) * F x (arcY x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [this, hsym] at hmain
  exact (neg_inj.mp hmain).symm

theorem subst_left :
    ∫ y in (Real.sqrt 3 / 2)..1, F (-arcX y) y = ∫ x in (-1 / 2 : ℝ)..0, (-(x / arcY x)) * F x (arcY x) := by
  have hmain := intervalIntegral.integral_deriv_smul_comp' (a := -1 / 2) (b := 0) (f := arcY)
    (f' := fun x => -x / arcY x) (g := fun y => F (-arcX y) y)
    (fun x hx => by
      rw [uIcc_of_le (by norm_num)] at hx
      exact arcY_hasDerivAt (by rw [abs_of_nonpos hx.2]; linarith [hx.1]))
    (arcY_deriv_cont.mono (by rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl (by norm_num)))
    (h.continuousOn_negarcX_F (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hy
      rw [uIcc_of_le (by norm_num)] at hx
      exact arcY_pos (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)))
  rw [arcY_neg_half, arcY_zero] at hmain
  have hcongr : ∫ x in (-1 / 2 : ℝ)..0, (-x / arcY x) • F (-arcX (arcY x)) (arcY x) =
      ∫ x in (-1 / 2 : ℝ)..0, (-(x / arcY x)) * F x (arcY x) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le (by norm_num)] at hx
    rw [arcX_arcY_abs (by rw [abs_of_nonpos hx.2]; linarith [hx.1]), abs_of_nonpos hx.2,
      neg_neg, Complex.real_smul]
    push_cast
    ring
  simp only [Function.comp_apply] at hmain
  rw [hcongr] at hmain
  exact hmain.symm


theorem continuousOn_arc_F : ContinuousOn (fun x : ℝ => F x (arcY x)) (Icc (-1 / 2) (1 / 2)) :=
  h.cF.comp (continuous_id.prodMk arcY_continuous).continuousOn (fun x hx =>
    arcY_pos (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩))

theorem continuousOn_dens : ContinuousOn (fun x : ℝ => (x : ℂ) / (arcY x : ℂ) * F x (arcY x))
    (Icc (-1 / 2) (1 / 2)) := by
  refine ContinuousOn.mul (ContinuousOn.div Complex.continuous_ofReal.continuousOn
    (Complex.continuous_ofReal.comp arcY_continuous).continuousOn (fun x hx => ?_)) h.continuousOn_arc_F
  exact_mod_cast (arcY_pos (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)).ne'

theorem J_eq {T : ℝ} (hT : 1 ≤ T) :
    ∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T, Fx x y =
      -∫ x in (-1 / 2 : ℝ)..(1 / 2), (x : ℂ) / (arcY x : ℂ) * F x (arcY x) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Fx p.1 p.2) (regionF T) :=
    h.cFx.mono (fun p hp => regionF_pos hp)
  rw [swap_region Fx T hT hcont]
  have hle : Real.sqrt 3 / 2 ≤ 1 := sqrt3_half_le_one
  have hinner : ∀ y ∈ uIcc (Real.sqrt 3 / 2) T,
      ((∫ x in (-1 / 2 : ℝ)..(-arcX y), Fx x y) + ∫ x in arcX y..(1 / 2), Fx x y) =
        F (-arcX y) y - F (arcX y) y := by
    intro y hy
    rw [uIcc_of_le (hle.trans hT)] at hy
    have hy0 : 0 < y := lt_of_lt_of_le sqrt3_half_pos hy.1
    have hr := arcX_nonneg y
    have hr2 := arcX_le_half hy.1
    rw [h.integral_Fx hy0 (by linarith), h.integral_Fx hy0 (by linarith), h.per y hy0]
    ring
  rw [intervalIntegral.integral_congr hinner]
  have hc1 : ContinuousOn (fun y => F (-arcX y) y) (Icc (Real.sqrt 3 / 2) T) :=
    h.continuousOn_negarcX_F (fun y hy => lt_of_lt_of_le sqrt3_half_pos hy.1)
  have hc2 : ContinuousOn (fun y => F (arcX y) y) (Icc (Real.sqrt 3 / 2) T) :=
    h.continuousOn_arcX_F (fun y hy => lt_of_lt_of_le sqrt3_half_pos hy.1)
  have hi1 : ∀ a b, Real.sqrt 3 / 2 ≤ a → a ≤ b → b ≤ T →
      IntervalIntegrable (fun y => F (-arcX y) y) volume a b := fun a b ha hab hb =>
    (hc1.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hi2 : ∀ a b, Real.sqrt 3 / 2 ≤ a → a ≤ b → b ≤ T →
      IntervalIntegrable (fun y => F (arcX y) y) volume a b := fun a b ha hab hb =>
    (hc2.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)]
  · have hz : ∫ y in (1 : ℝ)..T, (F (-arcX y) y - F (arcX y) y) = 0 := by
      have : ∀ y ∈ uIcc (1 : ℝ) T, F (-arcX y) y - F (arcX y) y = 0 := by
        intro y hy
        rw [uIcc_of_le hT] at hy
        rw [arcX_eq_zero_of_one_le hy.1]
        simp
      rw [intervalIntegral.integral_congr this]; simp
    rw [hz, add_zero, intervalIntegral.integral_sub (hi1 _ _ le_rfl hle hT)
      (hi2 _ _ le_rfl hle hT), subst_left h, subst_right h]
    have hsplit : ∫ x in (-1 / 2 : ℝ)..(1 / 2), (x : ℂ) / (arcY x : ℂ) * F x (arcY x) =
        (∫ x in (-1 / 2 : ℝ)..0, (x : ℂ) / (arcY x : ℂ) * F x (arcY x)) +
          ∫ x in (0 : ℝ)..(1 / 2), (x : ℂ) / (arcY x : ℂ) * F x (arcY x) := by
      refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
      · exact (h.continuousOn_dens.mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable
      · exact (h.continuousOn_dens.mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable
    rw [hsplit]
    have hneg : ∫ x in (-1 / 2 : ℝ)..0, (-((x : ℂ) / (arcY x : ℂ))) * F x (arcY x) =
        -∫ x in (-1 / 2 : ℝ)..0, (x : ℂ) / (arcY x : ℂ) * F x (arcY x) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      ring
    rw [hneg]; ring
  · exact (hi1 _ _ le_rfl hle hT).sub (hi2 _ _ le_rfl hle hT)
  · exact (hi1 _ _ hle hT le_rfl).sub (hi2 _ _ hle hT le_rfl)


/-- **Green's formula on the truncated fundamental domain of `SL₂(ℤ)`**, in real form. -/
theorem stokes_real {T : ℝ} (hT : 1 ≤ T)
    (hodd : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), gArc F (-x) = - gArc F x) :
    ∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T, (Fx x y - Complex.I * Fy x y) =
      -Complex.I * ∫ x in (-1 / 2 : ℝ)..(1 / 2), F x T := by
  have hcontx : ContinuousOn (fun p : ℝ × ℝ => Fx p.1 p.2) (regionF T) :=
    h.cFx.mono (fun p hp => regionF_pos hp)
  have hconty : ContinuousOn (fun p : ℝ × ℝ => Fy p.1 p.2) (regionF T) :=
    h.cFy.mono (fun p hp => regionF_pos hp)
  have hAx := intervalIntegrable_inner Fx T hT hcontx
  have hAy := intervalIntegrable_inner Fy T hT hconty
  have hpos : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), 0 < arcY x := fun x hx =>
    arcY_pos (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
  have hinner : ∀ x ∈ uIcc (-1 / 2 : ℝ) (1 / 2),
      ∫ y in arcY x..T, (Fx x y - Complex.I * Fy x y) =
        (∫ y in arcY x..T, Fx x y) - Complex.I * (F x T - F x (arcY x)) := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hp := hpos x hx
    have hxT : arcY x ≤ T := (arcY_le_one x).trans hT
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, h.integral_Fy hp hxT]
    · exact (h.continuousOn_y_Fx hp |>.mono (fun y hy => by
        rw [uIcc_of_le hxT] at hy; exact hy.1)).intervalIntegrable
    · exact ((h.continuousOn_y_Fy hp |>.mono (fun y hy => by
        rw [uIcc_of_le hxT] at hy; exact hy.1)).intervalIntegrable).const_mul _
  rw [intervalIntegral.integral_congr hinner]
  have hFT : IntervalIntegrable (fun x => F x T) volume (-1 / 2) (1 / 2) :=
    (h.continuous_x_F (lt_of_lt_of_le one_pos hT)).intervalIntegrable _ _
  have hArc : IntervalIntegrable (fun x => F x (arcY x)) volume (-1 / 2) (1 / 2) :=
    (h.continuousOn_arc_F).intervalIntegrable_of_Icc (by norm_num)
  rw [intervalIntegral.integral_sub hAx, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hFT hArc,
    h.J_eq hT]
  · have hg := integral_gArc_eq_zero F hodd
    have hg' : ∫ x in (-1 / 2 : ℝ)..(1 / 2), gArc F x =
        (∫ x in (-1 / 2 : ℝ)..(1 / 2), (x : ℂ) / (arcY x : ℂ) * F x (arcY x)) -
          Complex.I * ∫ x in (-1 / 2 : ℝ)..(1 / 2), F x (arcY x) := by
      have hd : IntervalIntegrable (fun x : ℝ => (x : ℂ) / (arcY x : ℂ) * F x (arcY x)) volume (-1 / 2) (1 / 2) :=
        h.continuousOn_dens.intervalIntegrable_of_Icc (by norm_num)
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hd (hArc.const_mul _)]
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [uIcc_of_le (by norm_num)] at hx
      exact gArc_eq F x (hpos x hx).ne'
    rw [hg] at hg'
    linear_combination hg'
  · exact (hFT.sub hArc).const_mul _

end StokesData


end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
