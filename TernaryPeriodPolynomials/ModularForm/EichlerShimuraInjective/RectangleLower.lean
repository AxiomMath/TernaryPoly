module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.ArcSymmetry

@[expose] public section


/-!
# A rectangle bounds the truncated integral from below

`J_lower`: for `p ≥ 0` continuous and `p ≥ e` on a rectangle in `[-1/2, 1/2] × [1, T]`, the iterated integral over the truncated fundamental domain is at least `e · area`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

/-- A lower bound for an iterated integral over the truncated fundamental domain by a rectangle. -/
theorem J_lower (p : ℝ → ℝ → ℝ) (hp0 : ∀ x y, 0 < y → 0 ≤ p x y)
    (hpc : ContinuousOn (fun q : ℝ × ℝ => p q.1 q.2) {q | 0 < q.2}) {T : ℝ} (hT : 1 ≤ T)
    {a b c d e : ℝ} (ha : -1 / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hc : 1 ≤ c) (hcd : c ≤ d) (hdT : d ≤ T)
    (_he : 0 ≤ e) (hpe : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, e ≤ p x y) :
    e * (b - a) * (d - c) ≤ ∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T, p x y := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => ((p q.1 q.2 : ℝ) : ℂ)) (regionF T) :=
    Complex.continuous_ofReal.comp_continuousOn (hpc.mono (fun q hq => regionF_pos hq))
  have hint : IntervalIntegrable (fun x => ∫ y in arcY x..T, p x y) volume (-1 / 2) (1 / 2) := by
    have h := intervalIntegrable_inner (fun x y => ((p x y : ℝ) : ℂ)) T hT hcont
    have h2 : IntervalIntegrable (fun x => (∫ y in arcY x..T, ((p x y : ℝ) : ℂ)).re) volume (-1 / 2) (1 / 2) :=
      ⟨h.1.re, h.2.re⟩
    refine h2.congr ?_
    intro x _
    simp only []
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have hxpos : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), 0 ≤ ∫ y in arcY x..T, p x y := by
    intro x hx
    refine intervalIntegral.integral_nonneg ((arcY_le_one x).trans hT) (fun y hy => hp0 x y ?_)
    have : 0 < arcY x := arcY_pos (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
    linarith [hy.1]
  have hlow : ∀ x ∈ Icc a b, e * (d - c) ≤ ∫ y in arcY x..T, p x y := by
    intro x hx
    have hap : 0 < arcY x := arcY_pos (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have harc : arcY x ≤ c := (arcY_le_one x).trans hc
    have hcontx : ContinuousOn (fun y => p x y) (Icc (arcY x) T) := by
      refine (hpc.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ?_))
      show 0 < y
      exact lt_of_lt_of_le hap hy.1
    have hI1 : IntervalIntegrable (fun y => p x y) volume (arcY x) T :=
      hcontx.intervalIntegrable_of_Icc ((arcY_le_one x).trans hT)
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (arcY x) T)] (fun y => p x y) := by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall (fun y hy => ?_))
      exact hp0 x y (lt_trans hap hy.1)
    have hmono := intervalIntegral.integral_mono_interval (μ := volume) (f := fun y => p x y) harc hcd hdT hnn hI1
    have hI2 : IntervalIntegrable (fun y => p x y) volume c d :=
      hI1.mono_set (by
        rw [uIcc_of_le hcd, uIcc_of_le ((arcY_le_one x).trans hT)]
        exact Icc_subset_Icc harc hdT)
    have hm2 := intervalIntegral.integral_mono_on hcd (intervalIntegrable_const (c := e)) hI2
      (fun y hy => hpe x hx y hy)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm2
    linarith
  have hI3 : IntervalIntegrable (fun x => ∫ y in arcY x..T, p x y) volume a b :=
    hint.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
      exact Icc_subset_Icc ha hb)
  have hnn2 : 0 ≤ᵐ[volume.restrict (Ioc (-1 / 2 : ℝ) (1 / 2))] (fun x => ∫ y in arcY x..T, p x y) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    exact hxpos x ⟨hx.1.le, hx.2⟩
  have hmono2 := intervalIntegral.integral_mono_interval (μ := volume)
    (f := fun x => ∫ y in arcY x..T, p x y) ha hab hb hnn2 hint
  have hm3 := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := e * (d - c))) hI3 hlow
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hm3
  nlinarith

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
