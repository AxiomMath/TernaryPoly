module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Fubini

@[expose] public section


/-!
# The arc term of Green's formula

Differentiability of the arc and the vanishing of the integral `∫ gArc` over the arc for an odd density, the arc contribution to Green's formula under `z ↦ -1/z`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open scoped ComplexConjugate

theorem arcY_hasDerivAt {x : ℝ} (hx : |x| < 1) : HasDerivAt arcY (-x / arcY x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have hpos : 1 - x ^ 2 ≠ 0 := by
    have : x ^ 2 < 1 := by
      have := abs_lt.mp hx
      nlinarith
    linarith
  have := h1.sqrt hpos
  unfold arcY
  convert this using 1
  have hx2 : 0 < Real.sqrt (1 - x ^ 2) := by
    apply Real.sqrt_pos.mpr
    have : x ^ 2 < 1 := by
      have := abs_lt.mp hx
      nlinarith
    linarith
  field_simp

theorem arcX_arcY {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : arcX (arcY x) = x := by
  unfold arcX arcY
  rw [Real.sq_sqrt (by nlinarith)]
  rw [show 1 - (1 - x ^ 2) = x ^ 2 by ring]
  exact Real.sqrt_sq hx


theorem arcX_continuous' : Continuous arcX := by unfold arcX; fun_prop

theorem arcX_arcY_abs {x : ℝ} (hx : |x| ≤ 1) : arcX (arcY x) = |x| := by
  unfold arcX arcY
  rw [Real.sq_sqrt (by nlinarith [abs_le.mp hx, sq_abs x, abs_nonneg x, sq_nonneg x]),
    show 1 - (1 - x ^ 2) = |x| ^ 2 by rw [sq_abs]; ring]
  exact Real.sqrt_sq (abs_nonneg x)

theorem arcY_zero : arcY 0 = 1 := by unfold arcY; simp

theorem arcY_half : arcY (1 / 2) = Real.sqrt 3 / 2 := by
  unfold arcY
  rw [show (1:ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num, Real.sqrt_div (by norm_num),
    show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem arcY_neg_half : arcY (-1 / 2) = Real.sqrt 3 / 2 := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring]
  unfold arcY
  rw [show (1:ℝ) - (-(1 / 2)) ^ 2 = 3 / 4 by norm_num, Real.sqrt_div (by norm_num),
    show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem arcY_pos {x : ℝ} (hx : |x| ≤ 1 / 2) : 0 < arcY x :=
  lt_of_lt_of_le (by positivity) (sqrt3_div_two_le_arcY hx)

theorem sqrt3_half_pos : 0 < Real.sqrt 3 / 2 := by positivity

theorem sqrt3_half_le_one : Real.sqrt 3 / 2 ≤ 1 := by
  have : Real.sqrt 3 ≤ 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

theorem arcX_eq_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) : arcX y = 0 := by
  unfold arcX
  exact Real.sqrt_eq_zero_of_nonpos (by nlinarith)

theorem regionF_pos {T : ℝ} {p : ℝ × ℝ} (hp : p ∈ regionF T) : 0 < p.2 := by
  obtain ⟨h1, h2, h3, -⟩ := hp
  exact lt_of_lt_of_le (arcY_pos (abs_le.mpr ⟨by linarith, h2⟩)) h3


theorem arcY_deriv_cont : ContinuousOn (fun x : ℝ => -x / arcY x) (uIcc (-1 / 2) (1 / 2)) := by
  refine ContinuousOn.div (continuous_neg.continuousOn) arcY_continuous.continuousOn (fun x hx => ?_)
  rw [uIcc_of_le (by norm_num)] at hx
  exact (arcY_pos (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)).ne'

section GArc
variable (F : ℝ → ℝ → ℂ)
/-- The arc integrand whose oddness is the `S`-invariance on the unit circle. -/
def gArc (F : ℝ → ℝ → ℂ) (x : ℝ) : ℂ := F x (arcY x) * ((x : ℂ) - Complex.I * (arcY x : ℂ)) / (arcY x : ℂ)

theorem gArc_eq (x : ℝ) (hx : arcY x ≠ 0) :
    gArc F x = (x : ℂ) / (arcY x : ℂ) * F x (arcY x) - Complex.I * F x (arcY x) := by
  have : (arcY x : ℂ) ≠ 0 := by exact_mod_cast hx
  unfold gArc
  field_simp

theorem integral_gArc_eq_zero (hodd : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), gArc F (-x) = - gArc F x) :
    ∫ x in (-1 / 2 : ℝ)..(1 / 2), gArc F x = 0 := by
  have h1 := intervalIntegral.integral_comp_neg (a := (-1 / 2 : ℝ)) (b := 1 / 2) (gArc F)
  have e1 : -(1 / 2 : ℝ) = -1 / 2 := by ring
  have e2 : -(-1 / 2 : ℝ) = 1 / 2 := by ring
  rw [e1, e2] at h1
  have h2 : ∫ x in (-1 / 2 : ℝ)..(1 / 2), gArc F (-x) = -∫ x in (-1 / 2 : ℝ)..(1 / 2), gArc F x := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le (by norm_num)] at hx
    exact hodd x hx
  rw [h2] at h1
  have : (2 : ℂ) * ∫ x in (-1 / 2 : ℝ)..(1 / 2), gArc F x = 0 := by
    linear_combination -h1
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

end GArc

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
