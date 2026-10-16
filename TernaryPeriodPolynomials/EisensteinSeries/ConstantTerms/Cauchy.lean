module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Convergence
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Compact
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

@[expose] public section


/-!
# Cauchy estimates for the slash transform `h_A` (Appendix C.3)

On the disc `|τ - i| ≤ 1/2` the weight-`(n+3)` slash transform `h_A` of a function with
`‖h(τ)‖ (Im τ)^{(n+3)/2} ≤ C_h` satisfies `|h_A| ≤ C_h 2^{(n+3)/2} t^{-(n+3)/2}`, hence all its
derivatives at `i` obey the same bound (times `j! 2^j`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### Cauchy estimates for the slash transform `h_A` -/

/-- The open upper half-plane in `ℂ`. -/
def upperHalf : Set ℂ := {τ | 0 < τ.im}

theorem isOpen_upperHalf : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im

theorem slashTwisted_planeA_apply (k : ℕ) (h : ℂ → ℂ) {p : Fin 5 → ℝ} (hp : p ∈ Omega) (τ : ℂ) :
    slashTwisted k (planeA p) h τ =
      (((Real.sqrt (p 3) / Real.sqrt (p 4)) ^ k : ℝ) : ℂ) * h (((p 3 : ℝ) : ℂ) * τ + (p 2 : ℂ)) := by
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hp
  have hsa : Real.sqrt (p 3) = a := by rw [e3]; exact Real.sqrt_sq ha.le
  have hsb : Real.sqrt (p 4) = b := by rw [e4]; exact Real.sqrt_sq hb.le
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hy : (p 3 : ℂ) = (a : ℂ) ^ 2 := by exact_mod_cast e3
  unfold slashTwisted
  have harg : ((planeA p 0 0 : ℝ) * τ + (planeA p 0 1 : ℝ)) / ((planeA p 1 0 : ℝ) * τ + (planeA p 1 1 : ℝ))
      = ((p 3 : ℝ) : ℂ) * τ + (p 2 : ℂ) := by
    simp [planeA, hsa, hsb, hy]
    field_simp
  simp only [Matrix.det_fin_two] at *
  rw [harg]
  congr 1
  simp [planeA, hsa, hsb]
  rw [← inv_pow, ← mul_pow]
  congr 1
  field_simp

theorem differentiableOn_hA (k : ℕ) {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h upperHalf)
    {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    DifferentiableOn ℂ (slashTwisted k (planeA p) h) upperHalf := by
  have : slashTwisted k (planeA p) h = fun τ =>
      (((Real.sqrt (p 3) / Real.sqrt (p 4)) ^ k : ℝ) : ℂ) * h (((p 3 : ℝ) : ℂ) * τ + (p 2 : ℂ)) :=
    funext (slashTwisted_planeA_apply k h hp)
  rw [this]
  refine (differentiableOn_const _).mul ?_
  refine hd.comp ((differentiableOn_const _).mul differentiableOn_id |>.add (differentiableOn_const _))
    ?_
  intro τ hτ
  show 0 < (((p 3 : ℝ) : ℂ) * τ + (p 2 : ℂ)).im
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero]
  exact mul_pos hp.1 hτ

theorem hA_sphere_bound (n : ℕ) (h : ℂ → ℂ) (Ch : ℝ)
    (hh : ∀ τ : ℂ, 0 < τ.im → ‖h τ‖ * τ.im ^ (((n : ℝ) + 3) / 2) ≤ Ch)
    {p : Fin 5 → ℝ} (hp : p ∈ Omega) {z : ℂ} (hz : z ∈ Metric.sphere Complex.I (1 / 2)) :
    ‖slashTwisted (n + 3) (planeA p) h z‖ ≤
      Ch * 2 ^ (((n : ℝ) + 3) / 2) / (Real.sqrt (p 4)) ^ (n + 3) := by
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hp
  have hsa : Real.sqrt (p 3) = a := by rw [e3]; exact Real.sqrt_sq ha.le
  have hsb : Real.sqrt (p 4) = b := by rw [e4]; exact Real.sqrt_sq hb.le
  have hzI : 1 / 2 ≤ z.im := by
    have := Complex.abs_im_le_norm (z - Complex.I)
    have h1 : ‖z - Complex.I‖ = 1 / 2 := by simpa using hz
    have h2 : |(z - Complex.I).im| ≤ 1 / 2 := by rw [← h1]; exact this
    have h3 := (abs_le.1 h2).1
    simp at h3
    linarith
  rw [slashTwisted_planeA_apply (n + 3) h hp, hsa, hsb, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (pow_pos (div_pos ha hb) _)]
  set w : ℂ := ((p 3 : ℝ) : ℂ) * z + (p 2 : ℂ) with hw
  have him : w.im = a ^ 2 * z.im := by
    have : w.im = p 3 * z.im := by simp [hw]
    rw [this, e3]
  have hwpos : 0 < w.im := by rw [him]; positivity
  have hs : 0 < w.im ^ (((n : ℝ) + 3) / 2) := Real.rpow_pos_of_pos hwpos _
  have h1 := hh w hwpos
  have hhw : ‖h w‖ ≤ Ch / w.im ^ (((n : ℝ) + 3) / 2) := by
    rw [le_div_iff₀ hs]; exact h1
  -- compare `w.im ≥ a^2 / 2`
  have hwim : a ^ 2 / 2 ≤ w.im := by rw [him]; nlinarith [sq_nonneg a]
  have hpow : (a ^ 2 / 2) ^ (((n : ℝ) + 3) / 2) ≤ w.im ^ (((n : ℝ) + 3) / 2) :=
    Real.rpow_le_rpow (by positivity) hwim (by positivity)
  have hCh : 0 ≤ Ch := by
    have := hh Complex.I (by simp)
    rw [Complex.I_im, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hq : (a ^ 2 / 2) ^ (((n : ℝ) + 3) / 2) = a ^ (n + 3) / 2 ^ (((n : ℝ) + 3) / 2) := by
    rw [Real.div_rpow (by positivity) (by norm_num), rpow_half_eq a ha n]
  calc (a / b) ^ (n + 3) * ‖h w‖ ≤ (a / b) ^ (n + 3) * (Ch / w.im ^ (((n : ℝ) + 3) / 2)) :=
        mul_le_mul_of_nonneg_left hhw (by positivity)
    _ ≤ (a / b) ^ (n + 3) * (Ch / (a ^ 2 / 2) ^ (((n : ℝ) + 3) / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact div_le_div_of_nonneg_left hCh (by positivity) hpow
    _ = Ch * 2 ^ (((n : ℝ) + 3) / 2) / b ^ (n + 3) := by
        rw [hq, div_pow]
        field_simp

theorem hA_iteratedFDeriv_bound (n : ℕ) (h : ℂ → ℂ) (Ch : ℝ)
    (hh : ∀ τ : ℂ, 0 < τ.im → ‖h τ‖ * τ.im ^ (((n : ℝ) + 3) / 2) ≤ Ch)
    (hd : DifferentiableOn ℂ h upperHalf) {p : Fin 5 → ℝ} (hp : p ∈ Omega) (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i (slashTwisted (n + 3) (planeA p) h) upperHalf Complex.I‖ ≤
      (i.factorial : ℝ) * (Ch * 2 ^ (((n : ℝ) + 3) / 2) / (Real.sqrt (p 4)) ^ (n + 3)) * 2 ^ i := by
  have hdA := differentiableOn_hA (n + 3) hd hp
  have hI : Complex.I ∈ upperHalf := by simp [upperHalf]
  have hcd : ContDiffAt ℂ ⊤ (slashTwisted (n + 3) (planeA p) h) Complex.I :=
    (hdA.contDiffOn isOpen_upperHalf).contDiffAt (isOpen_upperHalf.mem_nhds hI)
  rw [iteratedFDerivWithin_of_isOpen i isOpen_upperHalf hI]
  have hcd' : ContDiffAt ℂ i (slashTwisted (n + 3) (planeA p) h) Complex.I :=
    hcd.of_le (by exact_mod_cast le_top)
  have hr := hcd'.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  calc ‖iteratedFDeriv ℝ i (slashTwisted (n + 3) (planeA p) h) Complex.I‖
      = ‖(ContinuousMultilinearMap.restrictScalars ℝ
          (iteratedFDeriv ℂ i (slashTwisted (n + 3) (planeA p) h) Complex.I))‖ := by
        rw [← hr]; rfl
    _ ≤ ‖iteratedFDeriv ℂ i (slashTwisted (n + 3) (planeA p) h) Complex.I‖ := by
        rw [ContinuousMultilinearMap.norm_restrictScalars]
    _ = ‖iteratedDeriv i (slashTwisted (n + 3) (planeA p) h) Complex.I‖ :=
        norm_iteratedFDeriv_eq_norm_iteratedDeriv
    _ ≤ (i.factorial : ℝ) * (Ch * 2 ^ (((n : ℝ) + 3) / 2) / (Real.sqrt (p 4)) ^ (n + 3)) /
          (1 / 2) ^ i := by
        refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i (by norm_num) ?_
          (fun z hz => hA_sphere_bound n h Ch hh hp hz)
        refine hdA.diffContOnCl_ball ?_
        intro z hz
        have hz' : ‖z - Complex.I‖ ≤ 1 / 2 := by
          rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hz
        have h2 : |(z - Complex.I).im| ≤ 1 / 2 := (Complex.abs_im_le_norm _).trans hz'
        have h3 := (abs_le.1 h2).1
        simp at h3
        show 0 < z.im
        linarith
    _ = _ := by
        rw [div_eq_mul_inv, one_div, inv_pow, inv_inv]

end TernaryPeriodPolynomials.Argument.ConvergenceC4
