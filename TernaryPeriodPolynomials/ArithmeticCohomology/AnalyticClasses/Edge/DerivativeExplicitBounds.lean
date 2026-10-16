module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitClosedForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.DoublingMeanValue

@[expose] public section


/-!
# Bounds for the closed form of the mixed derivative

With `α = √(1 + s²) ≤ R = √(1 + s² + t²)`, the quantities `E = i (R + α²) - s t` and
`N = i (R - α²) - s t` satisfy `‖N‖ < ‖E‖ ≤ 3 α R`, so the disc coordinate `w = N / E` lies in the
open unit disc. A strongly measurable function on `ℝ × ℝ` bounded by `C (1 + s² + t²)^{-p}` with
`p > 1` is integrable; the transfer scale `(√R)^{-(n+3)}` has norm `(1 + s² + t²)^{-(n+3)/4}`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

namespace EdgeExplicit

/-! ### Elementary inequalities -/

theorem one_le_gsAlpha (u : ℝ × ℝ) : 1 ≤ gsAlpha u := by
  rw [gsAlpha]
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg u.1])

theorem one_le_gsRadius (u : ℝ × ℝ) : 1 ≤ gsRadius u := by
  rw [gsRadius]
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg u.1, sq_nonneg u.2])

theorem gsAlpha_le_gsRadius (u : ℝ × ℝ) : gsAlpha u ≤ gsRadius u := by
  rw [gsAlpha, gsRadius]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u.2])

theorem holE_re (u : ℝ × ℝ) : (holE u).re = -(u.1 * u.2) := by
  simp [holE, ← Complex.ofReal_pow]

theorem holN_re (u : ℝ × ℝ) : (holN u).re = -(u.1 * u.2) := by
  simp [holN, ← Complex.ofReal_pow]

theorem holN_im (u : ℝ × ℝ) : (holN u).im = gsRadius u - gsAlpha u ^ 2 := by
  simp [holN, ← Complex.ofReal_pow]

theorem antiE_re (u : ℝ × ℝ) : (antiE u).re = u.1 * u.2 := by
  simp [antiE, ← Complex.ofReal_pow]

theorem antiN_re (u : ℝ × ℝ) : (antiN u).re = u.1 * u.2 := by
  simp [antiN, ← Complex.ofReal_pow]

theorem antiN_im (u : ℝ × ℝ) : (antiN u).im = gsRadius u - gsAlpha u ^ 2 := by
  simp [antiN, ← Complex.ofReal_pow]

theorem norm_le_of_parts {z : ℂ} {b : ℝ} (hb : 0 ≤ b) (h : z.re ^ 2 + z.im ^ 2 ≤ b ^ 2) :
    ‖z‖ ≤ b := by
  rw [← Real.sqrt_sq hb, Complex.norm_eq_sqrt_sq_add_sq]
  exact Real.sqrt_le_sqrt h

theorem parts_bound (u : ℝ × ℝ) (x y : ℝ) (hx : x ^ 2 = (u.1 * u.2) ^ 2)
    (hy : y = gsRadius u + gsAlpha u ^ 2) :
    x ^ 2 + y ^ 2 ≤ (3 * gsAlpha u * gsRadius u) ^ 2 := by
  have h1 := one_le_gsAlpha u
  have h2 := gsAlpha_le_gsRadius u
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  have hs : u.1 ^ 2 ≤ gsAlpha u ^ 2 := by nlinarith
  have ht : u.2 ^ 2 ≤ gsRadius u ^ 2 := by nlinarith
  have hst : (u.1 * u.2) ^ 2 ≤ (gsAlpha u * gsRadius u) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul hs ht (sq_nonneg _) (sq_nonneg _)
  have hy' : y ≤ 2 * gsAlpha u * gsRadius u := by
    rw [hy]
    nlinarith
  have hy0 : 0 ≤ y := by
    rw [hy]
    have := gsRadius_pos u
    positivity
  nlinarith

theorem norm_holE_le (u : ℝ × ℝ) : ‖holE u‖ ≤ 3 * gsAlpha u * gsRadius u := by
  have := gsAlpha_pos u
  have := gsRadius_pos u
  exact norm_le_of_parts (by positivity)
    (parts_bound u _ _ (by rw [holE_re]; ring) (holE_im u))

theorem norm_antiE_le (u : ℝ × ℝ) : ‖antiE u‖ ≤ 3 * gsAlpha u * gsRadius u := by
  have := gsAlpha_pos u
  have := gsRadius_pos u
  exact norm_le_of_parts (by positivity) (parts_bound u _ _ (by rw [antiE_re]) (antiE_im u))

theorem norm_lt_of_parts {z w : ℂ} (hre : z.re = w.re) (him : z.im ^ 2 < w.im ^ 2) :
    ‖z‖ < ‖w‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq, hre]
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

theorem im_sq_lt (u : ℝ × ℝ) :
    (gsRadius u - gsAlpha u ^ 2) ^ 2 < (gsRadius u + gsAlpha u ^ 2) ^ 2 := by
  have := gsAlpha_pos u
  have := gsRadius_pos u
  nlinarith [pow_pos (gsAlpha_pos u) 2]

theorem norm_holDisc_lt_one (u : ℝ × ℝ) : ‖holDisc u‖ < 1 := by
  rw [holDisc, norm_div, div_lt_one (norm_pos_iff.mpr (holE_ne_zero u))]
  exact norm_lt_of_parts (by rw [holN_re, holE_re]) (by rw [holN_im, holE_im]; exact im_sq_lt u)

theorem norm_antiDisc_lt_one (u : ℝ × ℝ) : ‖antiDisc u‖ < 1 := by
  rw [antiDisc, norm_div, div_lt_one (norm_pos_iff.mpr (antiE_ne_zero u))]
  exact norm_lt_of_parts (by rw [antiN_re, antiE_re])
    (by rw [antiN_im, antiE_im]; exact im_sq_lt u)

/-! ### Decay and integrability -/

/-- A measurable function on `ℝ × ℝ` bounded by `C (1 + s² + t²)^{-p}`, `p > 1`, is integrable. -/
theorem integrable_of_decay {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : AEStronglyMeasurable f) {C p : ℝ} (hp : 1 < p)
    (bound : ∀ u : ℝ × ℝ, ‖f u‖ ≤ C * (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-p)) : Integrable f :=
  Integrable.mono' ((integral_one_add_sq_rpow_neg hp).1.const_mul C) hf
    (Filter.Eventually.of_forall bound)

theorem one_add_sq_pos (u : ℝ × ℝ) : 0 < 1 + u.1 ^ 2 + u.2 ^ 2 := by positivity

theorem sqrt_gsRadius_eq_rpow (u : ℝ × ℝ) :
    Real.sqrt (gsRadius u) = (1 + u.1 ^ 2 + u.2 ^ 2) ^ ((1 : ℝ) / 4) := by
  rw [gsRadius, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (one_add_sq_pos u).le]
  norm_num

theorem gsRadius_eq_rpow (u : ℝ × ℝ) :
    gsRadius u = (1 + u.1 ^ 2 + u.2 ^ 2) ^ ((1 : ℝ) / 2) := by
  rw [gsRadius, Real.sqrt_eq_rpow]

/-- **The norm of the transfer scale.** -/
theorem norm_inv_sqrt_pow (u : ℝ × ℝ) (k : ℕ) :
    ‖((Real.sqrt (gsRadius u) : ℂ) ^ k)⁻¹‖ = (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-((k : ℝ) / 4)) := by
  rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    sqrt_gsRadius_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (one_add_sq_pos u).le,
    Real.rpow_neg (one_add_sq_pos u).le]
  congr 2
  ring

theorem norm_inv_gsRadius_pow (u : ℝ × ℝ) (k : ℕ) :
    ‖((gsRadius u : ℂ) ^ k)⁻¹‖ = (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-((k : ℝ) / 2)) := by
  rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (gsRadius_pos u).le,
    gsRadius_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (one_add_sq_pos u).le,
    Real.rpow_neg (one_add_sq_pos u).le]
  congr 2
  ring

end EdgeExplicit

end TernaryPeriodPolynomials.AnalyticClasses
