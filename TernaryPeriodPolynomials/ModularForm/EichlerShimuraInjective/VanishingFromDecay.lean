module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Density
public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.RectangleLower

@[expose] public section


/-!
# Vanishing of `f` from decay of the coset integral

`f_zero_of_decay`: if `∫ Ã(x + iT) dx → 0` then `f = 0` (positivity of the Petersson density).

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane MeasureTheory Set intervalIntegral Filter Topology
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

section Final

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {n : ℕ} {f g : ℂ → ℂ} {Gf Gg : ℕ → ℂ → ℂ}
  {v : MvPolynomial (Fin 2) ℂ}

/-- The truncated fundamental-domain integral of the density. -/
def Jint (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ) (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  ∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T, pr Γ n f ((x : ℂ) + (y : ℂ) * Complex.I)

theorem stokes_J (S : Setup Γ n f g Gf Gg v) {T : ℝ} (hT : 1 ≤ T) :
    (2 * Complex.I) ^ (n + 1) * ((Jint Γ n f T : ℝ) : ℂ) =
      -(Complex.I / 2) * ∫ x in (-1 / 2 : ℝ)..(1 / 2),
        Atil Γ (Aval n f Gf Gg v) ((x : ℂ) + (T : ℂ) * Complex.I) := by
  rw [← stokes_Atil S hT]
  unfold Jint
  simp_rw [DAtil_eq]
  have h1 : ∀ x : ℝ, ∫ y in arcY x..T, (2 * Complex.I) ^ (n + 1) * ((pr Γ n f ((x : ℂ) + (y : ℂ) * Complex.I) : ℝ) : ℂ) =
      (2 * Complex.I) ^ (n + 1) * ((∫ y in arcY x..T, pr Γ n f ((x : ℂ) + (y : ℂ) * Complex.I) : ℝ) : ℂ) := by
    intro x
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]

theorem Jint_tendsto (S : Setup Γ n f g Gf Gg v)
    (hdec : Tendsto (fun T : ℝ => ∫ x in (-1 / 2 : ℝ)..(1 / 2),
      Atil Γ (Aval n f Gf Gg v) ((x : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 0)) :
    Tendsto (Jint Γ n f) atTop (𝓝 0) := by
  have hK : (2 * Complex.I) ^ (n + 1) ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hKn : 0 < ‖(2 * Complex.I) ^ (n + 1)‖ := norm_pos_iff.mpr hK
  have hn := hdec.norm
  rw [norm_zero] at hn
  have h2 : Tendsto (fun T : ℝ => ‖∫ x in (-1 / 2 : ℝ)..(1 / 2),
      Atil Γ (Aval n f Gf Gg v) ((x : ℂ) + (T : ℂ) * Complex.I)‖ / (2 * ‖(2 * Complex.I) ^ (n + 1)‖)) atTop
      (𝓝 0) := by
    simpa using hn.div_const (2 * ‖(2 * Complex.I) ^ (n + 1)‖)
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [eventually_ge_atTop 1] with T hT
  have := stokes_J S hT
  have hn2 := congrArg norm this
  rw [norm_mul, norm_mul, Complex.norm_real] at hn2
  have : ‖(-(Complex.I / 2) : ℂ)‖ = 1 / 2 := by simp
  rw [this] at hn2
  rw [le_div_iff₀ (by positivity)]
  nlinarith


theorem f_zero_of_decay (S : Setup Γ n f g Gf Gg v)
    (hdec : Tendsto (fun T : ℝ => ∫ x in (-1 / 2 : ℝ)..(1 / 2),
      Atil Γ (Aval n f Gf Gg v) ((x : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 0)) :
    ∀ z : ℂ, 0 < z.im → f z = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z1, hz1, hfz1⟩ := hcon
  let W : Set ℂ := {z : ℂ | |z.re| < 1 / 2 ∧ 1 < z.im ∧ z.im < 2}
  have hWopen : IsOpen W := by
    refine (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt Complex.continuous_im continuous_const))
  have hWU : W ⊆ Uset := fun z hz => by
    have := hz.2.1
    show 0 < z.im
    linarith
  obtain ⟨z0, hz0W, hfz0⟩ : ∃ z0 ∈ W, f z0 ≠ 0 := by
    by_contra hall
    push Not at hall
    have hstar : (3 / 2 : ℂ) * Complex.I ∈ W := by
      refine ⟨?_, ?_, ?_⟩ <;> norm_num [Complex.mul_re, Complex.mul_im]
    have hev : f =ᶠ[𝓝 ((3 / 2 : ℂ) * Complex.I)] 0 :=
      Filter.mem_of_superset (hWopen.mem_nhds hstar) (fun z hz => hall z hz)
    have hconv : IsPreconnected Uset := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
    have hustar : (3 / 2 : ℂ) * Complex.I ∈ Uset := hWU hstar
    have := (DifferentiableOn.analyticOnNhd S.hf isOpen_Uset).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconv hustar hev
    exact hfz1 (this hz1)
  have hz0U : 0 < z0.im := hWU hz0W
  set m : ℝ := ‖f z0‖ ^ 2 * z0.im ^ (n + 1) with hm
  have hmpos : 0 < m := by positivity
  have hρ : ContinuousAt (fun z : ℂ => ‖f z‖ ^ 2 * z.im ^ (n + 1)) z0 := by
    have hfc : ContinuousAt f z0 := (S.hf.continuousOn.continuousAt (isOpen_Uset.mem_nhds hz0U))
    exact (hfc.norm.pow 2).mul ((Complex.continuous_im.continuousAt).pow _)
  have hev := hρ.eventually (lt_mem_nhds (half_lt_self hmpos : m / 2 < m))
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.1 hev
  have hre := hz0W.1
  rw [abs_lt] at hre
  have hy1 := hz0W.2.1
  have hy2 := hz0W.2.2
  set r : ℝ := min (ε / 4) (min (1 / 2 - z0.re) (min (z0.re + 1 / 2) (min (z0.im - 1) (2 - z0.im)))) with hr
  have hrpos : 0 < r := by
    refine lt_min (by positivity) (lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))) <;> linarith [hre.1, hre.2]
  have hr1 : r ≤ ε / 4 := min_le_left _ _
  have hr2 : r ≤ 1 / 2 - z0.re := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ z0.re + 1 / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr4 : r ≤ z0.im - 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr5 : r ≤ 2 - z0.im :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let p : ℝ → ℝ → ℝ := fun x y => pr Γ n f ((x : ℂ) + (y : ℂ) * Complex.I)
  have hp0 : ∀ x y, 0 < y → 0 ≤ p x y := fun x y hy => pr_nonneg (by simpa using hy)
  have hpc : ContinuousOn (fun q : ℝ × ℝ => p q.1 q.2) {q | 0 < q.2} :=
    (continuousOn_pr S.hf).comp continuous_cxPt.continuousOn (fun q hq => cxPt_mem hq)
  have hbox : ∀ x ∈ Icc (z0.re - r) (z0.re + r), ∀ y ∈ Icc (z0.im - r) (z0.im + r), m / 2 ≤ p x y := by
    intro x hx y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy0
    have hd : dist ((x : ℂ) + (y : ℂ) * Complex.I) z0 < ε := by
      rw [dist_eq_norm]
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      have h1 : |x + (y * 0 - 0 * 1) - z0.re| ≤ r := by
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      have h2 : |0 + (y * 1 + 0 * 0) - z0.im| ≤ r := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      linarith
    have h1 := hεball hd
    have h2 := pr_ge S hz
    show m / 2 ≤ pr Γ n f ((x : ℂ) + (y : ℂ) * Complex.I)
    linarith
  have hJ := Jint_tendsto S hdec
  have hlow : ∀ T : ℝ, 2 ≤ T → (m / 2) * ((z0.re + r) - (z0.re - r)) * ((z0.im + r) - (z0.im - r)) ≤ Jint Γ n f T := by
    intro T hT
    exact J_lower p hp0 hpc (by linarith) (a := z0.re - r) (b := z0.re + r) (c := z0.im - r) (d := z0.im + r)
      (e := m / 2) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by positivity) hbox
  have hc0 : 0 < (m / 2) * ((z0.re + r) - (z0.re - r)) * ((z0.im + r) - (z0.im - r)) := by
    have : (z0.re + r) - (z0.re - r) = 2 * r := by ring
    have h' : (z0.im + r) - (z0.im - r) = 2 * r := by ring
    rw [this, h']; positivity
  have hev2 := (hJ.eventually (gt_mem_nhds hc0))
  obtain ⟨T, hT1, hT2⟩ := (hev2.and (eventually_ge_atTop 2)).exists
  exact absurd (hlow T hT2) (not_le.mpr hT1)

end Final

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
