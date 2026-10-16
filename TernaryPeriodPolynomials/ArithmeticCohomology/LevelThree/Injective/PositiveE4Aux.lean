module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.LowerBound
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

@[expose] public section


/-!
# `E₄` on the imaginary axis

For `t > 0` the value `E₄(i t) = 1 + 240 ∑ σ₃(n) e^{-2π n t}` is real (`E4_im`) and strictly
decreasing in `t` (`E4_re_strictAnti`). Using `E₄(i/u) = u⁴ E₄(i u)` this shows that
`A₄ = E₄(z) - E₄(3z)` and `B₄ = 81 E₄(3z) - E₄(z)` take positive real values on the positive
imaginary axis (`A4_pos`, `B4_pos`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThreeInjective.PositiveE4

open TernaryPeriodPolynomials.LevelThree.LevelThreeLowerBound

/-- The point `i t` of the upper half-plane. -/
def iPt (t : ℝ) (ht : 0 < t) : UpperHalfPlane :=
  ⟨Complex.I * (t : ℂ), by simpa using ht⟩

@[simp]
theorem coe_iPt (t : ℝ) (ht : 0 < t) : ((iPt t ht : UpperHalfPlane) : ℂ) = Complex.I * (t : ℂ) :=
  rfl

theorem ofComplex_I_mul (t : ℝ) (ht : 0 < t) :
    UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) = iPt t ht :=
  UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)

/-- The real series `∑ σ₃(n) rⁿ`. -/
def G (r : ℝ) : ℝ := ∑' n : ℕ+, (ArithmeticFunction.sigma 3 (n : ℕ) : ℝ) * r ^ (n : ℕ)

theorem summable_G {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun n : ℕ+ => (ArithmeticFunction.sigma 3 (n : ℕ) : ℝ) * r ^ (n : ℕ)) := by
  have hN : Summable (fun n : ℕ => (ArithmeticFunction.sigma 3 n : ℝ) * r ^ n) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_pow_mul_geometric_of_norm_lt_one 4 (r := r) (by rwa [Real.norm_of_nonneg h0]))
    have h4 : ArithmeticFunction.sigma 3 n ≤ n ^ 4 := ArithmeticFunction.sigma_le_pow_succ 3 n
    have h5 : (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast h4
    exact mul_le_mul_of_nonneg_right h5 (pow_nonneg h0 n)
  exact hN.comp_injective PNat.coe_injective

theorem G_strictMono {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1) : G r < G s := by
  unfold G
  refine Summable.tsum_lt_tsum (i := 1) (fun n => ?_) ?_ (summable_G hr.le (hrs.trans hs))
    (summable_G (hr.le.trans hrs.le) hs)
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrs.le _) (Nat.cast_nonneg _)
  · simpa [ArithmeticFunction.sigma_one] using hrs

/-- The real value of `E₄(i t)`. -/
def E4r (t : ℝ) : ℝ := 1 + 240 * G (Real.exp (-(2 * Real.pi * t)))

theorem E4_iPt (t : ℝ) (ht : 0 < t) : ModularForm.E₄ (iPt t ht) = ((E4r t : ℝ) : ℂ) := by
  have h := EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) ⟨2, rfl⟩ (iPt t ht)
  have hq : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((iPt t ht : UpperHalfPlane) : ℂ)) =
      ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) := by
    rw [coe_iPt, Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * t) * Complex.I_mul_I
  have hB : (bernoulli 4 : ℚ) = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
  have key : ∀ S : ℂ,
      1 - (2 * ((4 : ℕ) : ℂ) / ((bernoulli 4 : ℚ) : ℂ)) * S = 1 + 240 * S := by
    intro S
    rw [hB]
    push_cast
    ring
  rw [hq] at h
  have hS : (∑' n : ℕ+, ((ArithmeticFunction.sigma 3 (n : ℕ) : ℕ) : ℂ) *
      ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) ^ (n : ℤ)) =
        ((G (Real.exp (-(2 * Real.pi * t))) : ℝ) : ℂ) := by
    rw [G, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [zpow_natCast]
    simp
  refine (h.trans (key _)).trans ((congrArg (fun S : ℂ => 1 + 240 * S) hS).trans ?_)
  unfold E4r
  push_cast
  ring

theorem E4_im (t : ℝ) (ht : 0 < t) :
    (ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0 := by
  rw [ofComplex_I_mul t ht, E4_iPt t ht]
  exact Complex.ofReal_im _

theorem E4r_strictAnti {s t : ℝ} (hs : 0 < s) (hst : s < t) : E4r t < E4r s := by
  unfold E4r
  have hpi := mul_pos Real.pi_pos (sub_pos.mpr hst)
  have hr : Real.exp (-(2 * Real.pi * t)) < Real.exp (-(2 * Real.pi * s)) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hs1 : Real.exp (-(2 * Real.pi * s)) < 1 :=
    Real.exp_lt_one_iff.mpr (by have := mul_pos Real.pi_pos hs; linarith)
  have := G_strictMono (Real.exp_pos _) hr hs1
  linarith

theorem E4_re_strictAnti (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    (ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re <
      (ModularForm.E₄ (UpperHalfPlane.ofComplex (Complex.I * (s : ℂ)))).re := by
  have ht : 0 < t := hs.trans hst
  rw [ofComplex_I_mul t ht, ofComplex_I_mul s hs, E4_iPt t ht, E4_iPt s hs, Complex.ofReal_re,
    Complex.ofReal_re]
  exact E4r_strictAnti hs hst

theorem S_smul_iPt (u : ℝ) (hu : 0 < u) :
    ModularGroup.S • iPt u hu = iPt (1 / u) (by positivity) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  show (-((iPt u hu : UpperHalfPlane) : ℂ))⁻¹ = Complex.I * ((1 / u : ℝ) : ℂ)
  rw [coe_iPt]
  apply inv_eq_of_mul_eq_one_right
  calc -(Complex.I * (u : ℂ)) * (Complex.I * ((1 / u : ℝ) : ℂ))
      = -(Complex.I * Complex.I) * ((u : ℂ) * ((1 / u : ℝ) : ℂ)) := by ring
    _ = 1 := by
      rw [Complex.I_mul_I]
      push_cast
      field_simp

theorem E4r_inv {u : ℝ} (hu : 0 < u) : E4r (1 / u) = u ^ 4 * E4r u := by
  have h := E4_S (iPt u hu)
  rw [S_smul_iPt u hu, E4_iPt (1 / u) (by positivity), E4_iPt u hu, coe_iPt] at h
  have h4 : (Complex.I * (u : ℂ)) ^ 4 = (u : ℂ) ^ 4 := by
    rw [mul_pow]
    have : Complex.I ^ 4 = 1 := by
      linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq
    rw [this, one_mul]
  rw [h4] at h
  exact_mod_cast h

theorem smulH_iPt (t : ℝ) (ht : 0 < t) :
    smulH 3 (by norm_num) (iPt t ht) = iPt (3 * t) (by positivity) := by
  apply UpperHalfPlane.ext
  rw [coe_smulH, coe_iPt, coe_iPt]
  push_cast
  ring

theorem A4_iPt (t : ℝ) (ht : 0 < t) :
    dilFun 1 (-1) (iPt t ht) = ((E4r t - E4r (3 * t) : ℝ) : ℂ) := by
  unfold dilFun
  rw [smulH_iPt t ht, E4_iPt t ht, E4_iPt (3 * t) (by positivity)]
  push_cast
  ring

theorem B4_iPt (t : ℝ) (ht : 0 < t) :
    dilFun (-1) 81 (iPt t ht) = ((81 * E4r (3 * t) - E4r t : ℝ) : ℂ) := by
  unfold dilFun
  rw [smulH_iPt t ht, E4_iPt t ht, E4_iPt (3 * t) (by positivity)]
  push_cast
  ring

/-- `A₄ = E₄(z) - E₄(3z)` is a positive real number on the positive imaginary axis. -/
theorem A4_pos (t : ℝ) (ht : 0 < t) :
    0 < (dilFun 1 (-1) (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re ∧
      (dilFun 1 (-1) (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0 := by
  rw [ofComplex_I_mul t ht, A4_iPt t ht, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have := E4r_strictAnti ht (by linarith : t < 3 * t)
  linarith

/-- `B₄ = 81 E₄(3z) - E₄(z)` is a positive real number on the positive imaginary axis. -/
theorem B4_pos (t : ℝ) (ht : 0 < t) :
    0 < (dilFun (-1) 81 (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re ∧
      (dilFun (-1) 81 (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0 := by
  rw [ofComplex_I_mul t ht, B4_iPt t ht, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have hu : 0 < 3 * t := by positivity
  have h1 := E4r_inv hu
  have h2 := E4r_inv ht
  have h3 : E4r (1 / t) < E4r (1 / (3 * t)) :=
    E4r_strictAnti (one_div_pos.mpr hu) (one_div_lt_one_div_of_lt ht (by linarith))
  have e : t ^ 4 * (81 * E4r (3 * t) - E4r t) = E4r (1 / (3 * t)) - E4r (1 / t) := by
    rw [h1, h2]
    ring
  have hp : 0 < t ^ 4 := by positivity
  have : 0 < t ^ 4 * (81 * E4r (3 * t) - E4r t) := by rw [e]; linarith
  exact (mul_pos_iff_of_pos_left hp).mp this

end TernaryPeriodPolynomials.LevelThreeInjective.PositiveE4
