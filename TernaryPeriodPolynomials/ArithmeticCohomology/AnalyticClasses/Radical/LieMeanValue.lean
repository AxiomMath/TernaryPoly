module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.LieAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.DoublingMeanValue

@[expose] public section


/-!
# The obstruction shape integrates to zero

For `f` holomorphic on the upper half plane, the obstruction shape
`S_f(u) = α^{-(n+3)} ζ^{n+3} f(z(u))` has integral zero over `ℝ²` whenever it is integrable.
If `n + 3 = 2m` is even, `ζ² = α² (z² + 1) / R²` gives `S_f(u) = R^{-2m} H(w(u))` with
`H(w) = (c(w)² + 1)^m f(c(w))`, `c(w) = i (1 + w) / (1 - w)` the inverse Cayley transform and
`w(u) = (z(u) - i) / (z(u) + i) = -((R - 1) / (R + 1)) (s - i t)² / (s² + t²)`. Since `H` is
holomorphic on the unit disc with `H(0) = 0`, the angle-doubling mean value identity gives zero.
If `n + 3` is odd, `S_f` is odd under `u ↦ -u`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ}

namespace RadicalLie

open EdgeExplicit

/-! ### The Levi point and the unit -/

theorem goodPoint_im (u : ℝ × ℝ) : (goodPoint u).im = gsRadius u / gsAlpha u ^ 2 := by
  have h : goodPoint u = (((gsRadius u / gsAlpha u ^ 2 : ℝ) : ℂ)) * Complex.I +
      ((-(u.1 * u.2) / gsAlpha u ^ 2 : ℝ) : ℂ) := by
    have ha := gsAlpha_complex_ne_zero u
    rw [goodPoint]
    push_cast
    field_simp
    ring
  rw [h, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_im]
  ring

theorem goodPoint_im_pos (u : ℝ × ℝ) : 0 < (goodPoint u).im := by
  rw [goodPoint_im]
  have := gsRadius_pos u
  have := gsAlpha_pos u
  positivity

theorem continuous_goodPoint : Continuous goodPoint := by
  have ha (u : ℝ × ℝ) : (gsAlpha u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (gsAlpha_complex_ne_zero u)
  have hR : Continuous fun u : ℝ × ℝ => (gsRadius u : ℂ) :=
    Complex.continuous_ofReal.comp continuous_gsRadius
  have hα : Continuous fun u : ℝ × ℝ => (gsAlpha u : ℂ) :=
    Complex.continuous_ofReal.comp continuous_gsAlpha
  have h1 : Continuous fun u : ℝ × ℝ => (u.1 : ℂ) := Complex.continuous_ofReal.comp continuous_fst
  have h2 : Continuous fun u : ℝ × ℝ => (u.2 : ℂ) := Complex.continuous_ofReal.comp continuous_snd
  exact ((continuous_const.mul hR).sub (h1.mul h2)).div (hα.pow 2) ha

theorem continuous_radialUnit : Continuous radialUnit := by
  have hR : Continuous fun u : ℝ × ℝ => (gsRadius u : ℂ) :=
    Complex.continuous_ofReal.comp continuous_gsRadius
  have hα : Continuous fun u : ℝ × ℝ => (gsAlpha u : ℂ) :=
    Complex.continuous_ofReal.comp continuous_gsAlpha
  have h1 : Continuous fun u : ℝ × ℝ => (u.1 : ℂ) := Complex.continuous_ofReal.comp continuous_fst
  have h2 : Continuous fun u : ℝ × ℝ => (u.2 : ℂ) := Complex.continuous_ofReal.comp continuous_snd
  exact ((h1.mul hR).sub (continuous_const.mul h2)).div (hR.mul hα)
    fun u => mul_ne_zero (gsRadius_complex_ne_zero u) (gsAlpha_complex_ne_zero u)

/-- **`|ζ| ≤ 1`.** -/
theorem norm_radialUnit_le (u : ℝ × ℝ) : ‖radialUnit u‖ ≤ 1 := by
  have hR := gsRadius_pos u
  have hα := gsAlpha_pos u
  have hR2 := gsRadius_sq u
  have hα2 := gsAlpha_sq u
  rw [radialUnit, norm_div]
  refine div_le_one_of_le₀ ?_ (norm_nonneg _)
  have hden : ‖(gsRadius u : ℂ) * (gsAlpha u : ℂ)‖ = gsRadius u * gsAlpha u := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hden]
  have hnum : ‖(u.1 : ℂ) * (gsRadius u : ℂ) - Complex.I * (u.2 : ℂ)‖ ^ 2 =
      (u.1 * gsRadius u) ^ 2 + u.2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hsq : ‖(u.1 : ℂ) * (gsRadius u : ℂ) - Complex.I * (u.2 : ℂ)‖ ^ 2 ≤
      (gsRadius u * gsAlpha u) ^ 2 := by
    rw [hnum, mul_pow, mul_pow, hα2]
    nlinarith [sq_nonneg u.1, sq_nonneg u.2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-! ### The even case: the shape through the Cayley transform -/

theorem radialUnit_sq (u : ℝ × ℝ) :
    radialUnit u ^ 2 = (gsAlpha u : ℂ) ^ 2 * (goodPoint u ^ 2 + 1) / (gsRadius u : ℂ) ^ 2 := by
  have ha := gsAlpha_complex_ne_zero u
  have hr := gsRadius_complex_ne_zero u
  have identity : ((u.1 : ℂ) * gsRadius u - Complex.I * u.2) ^ 2 =
      (Complex.I * gsRadius u - u.1 * u.2) ^ 2 + (gsAlpha u : ℂ) ^ 4 := by
    linear_combination ((u.1 : ℂ) ^ 2 - Complex.I ^ 2) * gsRadius_complex_sq u +
      (-(gsAlpha u : ℂ) ^ 2 - (u.1 : ℂ) ^ 2 - 1) * gsAlpha_complex_sq u +
      (-(u.1 : ℂ) ^ 2 - 1) * Complex.I_sq
  rw [radialUnit, goodPoint, div_pow, identity]
  field_simp

theorem obstructionShape_even {m : ℕ} (hm : n + 3 = 2 * m) (f : ℂ → ℂ) (u : ℝ × ℝ) :
    obstructionShape n f u =
      ((gsRadius u : ℂ) ^ (n + 3))⁻¹ * (goodPoint u ^ 2 + 1) ^ m * f (goodPoint u) := by
  have ha := gsAlpha_complex_ne_zero u
  have hr := gsRadius_complex_ne_zero u
  rw [obstructionShape, hm, pow_mul, pow_mul, pow_mul, radialUnit_sq, div_pow, mul_pow]
  field_simp

/-- The inverse Cayley transform `c(w) = i (1 + w) / (1 - w)` of the unit disc onto the upper half
plane. -/
def cayleyInverse (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

theorem one_sub_ne_zero_of_mem_ball {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) : 1 - w ≠ 0 := by
  have hn : ‖w‖ < 1 := by simpa using hw
  intro h
  have : w = 1 := by linear_combination -h
  rw [this, norm_one] at hn
  exact lt_irrefl _ hn

theorem cayleyInverse_im_pos {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    0 < (cayleyInverse w).im := by
  have hn : ‖w‖ < 1 := by simpa using hw
  have hsq : w.re ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm w
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg w]
  have hpos : 0 < Complex.normSq (1 - w) :=
    Complex.normSq_pos.mpr (one_sub_ne_zero_of_mem_ball hw)
  rw [cayleyInverse, Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  rw [← sub_div]
  apply div_pos _ hpos
  nlinarith

theorem differentiableOn_cayleyInverse :
    DifferentiableOn ℂ cayleyInverse (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  exact ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id)
    (one_sub_ne_zero_of_mem_ball hw) |>.differentiableWithinAt

/-- The disc function `H(w) = (c(w)² + 1)^m f(c(w))`. -/
def discShape (m : ℕ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  (cayleyInverse w ^ 2 + 1) ^ m * f (cayleyInverse w)

theorem differentiableOn_discShape (m : ℕ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) :
    DifferentiableOn ℂ (discShape m f) (Metric.ball (0 : ℂ) 1) :=
  ((differentiableOn_cayleyInverse.pow 2).add_const 1 |>.pow m).mul
    (hf.comp differentiableOn_cayleyInverse fun _ hw => cayleyInverse_im_pos hw)

theorem discShape_zero {m : ℕ} (hm : m ≠ 0) (f : ℂ → ℂ) : discShape m f 0 = 0 := by
  simp [discShape, cayleyInverse, hm]

/-- The radial contraction `ψ(r) = (√(1 + r²) - 1) / (√(1 + r²) + 1)`. -/
def discRadius (r : ℝ) : ℝ := (Real.sqrt (1 + r ^ 2) - 1) / (Real.sqrt (1 + r ^ 2) + 1)

theorem one_le_sqrt_one_add_sq (r : ℝ) : 1 ≤ Real.sqrt (1 + r ^ 2) :=
  Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg r])

theorem continuous_discRadius : Continuous discRadius := by
  have hs : Continuous fun r : ℝ => Real.sqrt (1 + r ^ 2) := by fun_prop
  exact (hs.sub continuous_const).div (hs.add continuous_const)
    fun r => by linarith [one_le_sqrt_one_add_sq r]

theorem discRadius_nonneg (r : ℝ) : 0 ≤ discRadius r := by
  have := one_le_sqrt_one_add_sq r
  exact div_nonneg (by linarith) (by linarith)

theorem discRadius_lt_one (r : ℝ) : discRadius r < 1 := by
  have := one_le_sqrt_one_add_sq r
  rw [discRadius, div_lt_one (by linarith)]
  linarith

/-- The disc coordinate `w(u) = -ψ(|u|) (s - i t)² / (s² + t²)` of the good-line coordinate. -/
def discPoint (u : ℝ × ℝ) : ℂ :=
  -(discRadius (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) : ℂ) *
    (((u.1 : ℂ) - u.2 * Complex.I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2))

theorem discRadius_norm (u : ℝ × ℝ) :
    discRadius (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) = (gsRadius u - 1) / (gsRadius u + 1) := by
  rw [discRadius, Real.sq_sqrt (by positivity), ← add_assoc]
  rfl

theorem discPoint_mul (u : ℝ × ℝ) :
    discPoint u * (goodPoint u + Complex.I) = goodPoint u - Complex.I := by
  have ha := gsAlpha_complex_ne_zero u
  have hr := gsRadius_complex_ne_zero u
  by_cases hzero : (u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2 = 0
  · have hs : u.1 = 0 ∧ u.2 = 0 := by
      have real : u.1 ^ 2 + u.2 ^ 2 = 0 := by exact_mod_cast hzero
      constructor <;> nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    have hR : gsRadius u = 1 := by simp [gsRadius, hs.1, hs.2]
    have hα : gsAlpha u = 1 := by simp [gsAlpha, hs.1]
    rw [discPoint, hzero, div_zero, mul_zero, zero_mul, goodPoint, hR, hα, hs.1, hs.2]
    simp
  · have hplus : (gsRadius u : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < gsRadius u + 1 := by linarith [gsRadius_pos u]
      exact_mod_cast this.ne'
    have numerator : -((gsRadius u : ℂ) - 1) * ((u.1 : ℂ) - u.2 * Complex.I) ^ 2 *
        (Complex.I * ((gsRadius u : ℂ) + (gsAlpha u : ℂ) ^ 2) - u.1 * u.2) -
        ((gsRadius u : ℂ) + 1) * ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2) *
          (Complex.I * ((gsRadius u : ℂ) - (gsAlpha u : ℂ) ^ 2) - u.1 * u.2) = 0 := by
      linear_combination (-Complex.I * (Complex.I ^ 2 * (u.2 : ℂ) ^ 2 -
        2 * Complex.I * u.1 * u.2 + 2 * (u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2)) * gsRadius_complex_sq u +
        (Complex.I * (-Complex.I ^ 2 * gsRadius u * (u.2 : ℂ) ^ 2 + Complex.I ^ 2 * (u.2 : ℂ) ^ 2 +
          2 * Complex.I * gsRadius u * u.1 * u.2 - 2 * Complex.I * u.1 * u.2 +
          gsRadius u * (u.2 : ℂ) ^ 2 + 2 * (u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2)) *
          gsAlpha_complex_sq u +
        ((u.2 : ℂ) * (-Complex.I * gsRadius u * (u.1 : ℂ) ^ 2 * u.2 - Complex.I * (u.2 : ℂ) ^ 3 +
          2 * gsRadius u * (u.1 : ℂ) ^ 3 + gsRadius u * u.1 * (u.2 : ℂ) ^ 2 +
          u.1 * (u.2 : ℂ) ^ 2)) * Complex.I_sq
    rw [discPoint, discRadius_norm, goodPoint]
    push_cast
    rw [← sub_eq_zero]
    have expand : -(((gsRadius u : ℂ) - 1) / ((gsRadius u : ℂ) + 1)) *
          (((u.1 : ℂ) - u.2 * Complex.I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2)) *
          ((Complex.I * gsRadius u - u.1 * u.2) / (gsAlpha u : ℂ) ^ 2 + Complex.I) -
        ((Complex.I * gsRadius u - u.1 * u.2) / (gsAlpha u : ℂ) ^ 2 - Complex.I) =
        (-((gsRadius u : ℂ) - 1) * ((u.1 : ℂ) - u.2 * Complex.I) ^ 2 *
          (Complex.I * ((gsRadius u : ℂ) + (gsAlpha u : ℂ) ^ 2) - u.1 * u.2) -
          ((gsRadius u : ℂ) + 1) * ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2) *
            (Complex.I * ((gsRadius u : ℂ) - (gsAlpha u : ℂ) ^ 2) - u.1 * u.2)) /
        (((gsRadius u : ℂ) + 1) * ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2) * (gsAlpha u : ℂ) ^ 2) := by
      field_simp
      ring
    rw [expand, numerator, zero_div]

theorem norm_discPoint_lt (u : ℝ × ℝ) : ‖discPoint u‖ < 1 := by
  by_cases hzero : u = 0
  · simp [discPoint, hzero]
  have hu : (u.1, u.2) ≠ (0 : ℝ × ℝ) := by simpa using hzero
  rw [discPoint, norm_mul, norm_neg, Complex.norm_real, norm_doubling_factor hu, mul_one,
    Real.norm_of_nonneg (discRadius_nonneg _)]
  exact discRadius_lt_one _

theorem cayleyInverse_discPoint (u : ℝ × ℝ) : cayleyInverse (discPoint u) = goodPoint u := by
  have hne : 1 - discPoint u ≠ 0 :=
    one_sub_ne_zero_of_mem_ball (by simpa using norm_discPoint_lt u)
  rw [cayleyInverse, div_eq_iff hne]
  linear_combination discPoint_mul u

/-- The radial weight `φ(r) = (1 + r²)^{-m}`. -/
def radialWeight (m : ℕ) (r : ℝ) : ℝ := ((1 + r ^ 2) ^ m)⁻¹

theorem radialWeight_norm (m : ℕ) (u : ℝ × ℝ) :
    radialWeight m (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) = ((1 + u.1 ^ 2 + u.2 ^ 2) ^ m)⁻¹ := by
  rw [radialWeight, Real.sq_sqrt (by positivity), ← add_assoc]

theorem obstructionShape_even_disc {m : ℕ} (hm : n + 3 = 2 * m) (f : ℂ → ℂ) (u : ℝ × ℝ) :
    obstructionShape n f u =
      (radialWeight m (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) : ℂ) * discShape m f (discPoint u) := by
  rw [obstructionShape_even hm, discShape, cayleyInverse_discPoint, radialWeight_norm, hm,
    pow_mul, ← Complex.ofReal_pow, gsRadius_sq]
  push_cast
  ring

theorem integrable_radialWeight {m : ℕ} (hm : 1 < m) :
    Integrable fun u : ℝ × ℝ => radialWeight m (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) := by
  have hmass := (integral_one_add_sq_rpow_neg (a := (m : ℝ)) (by exact_mod_cast hm)).1
  refine hmass.congr (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [radialWeight_norm, Real.rpow_neg (by positivity), Real.rpow_natCast]

/-! ### The integral of the obstruction shape -/

theorem obstructionShape_neg (hn : Even n) (f : ℂ → ℂ) (u : ℝ × ℝ) :
    obstructionShape n f (-u) = -obstructionShape n f u := by
  have hR : gsRadius (-u) = gsRadius u := by simp [gsRadius]
  have hα : gsAlpha (-u) = gsAlpha u := by simp [gsAlpha]
  have hz : goodPoint (-u) = goodPoint u := by
    rw [goodPoint, goodPoint, hR, hα]
    simp
  have hζ : radialUnit (-u) = -radialUnit u := by
    rw [radialUnit, radialUnit, hR, hα]
    simp only [Prod.fst_neg, Prod.snd_neg, Complex.ofReal_neg]
    ring
  have hodd : Odd (n + 3) := by
    rcases hn with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  rw [obstructionShape, obstructionShape, hα, hz, hζ, hodd.neg_pow]
  ring

/-- **The obstruction shape of a holomorphic function integrates to zero.** -/
theorem integral_obstructionShape {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hint : Integrable (obstructionShape n f)) :
    ∫ u, obstructionShape n f u = 0 := by
  rcases Nat.even_or_odd n with hn | hn
  · have symmetric := integral_neg_eq_self (obstructionShape n f) (volume : Measure (ℝ × ℝ))
    simp only [obstructionShape_neg hn, integral_neg] at symmetric
    exact CharZero.eq_neg_self_iff.mp symmetric.symm
  · rcases hn with ⟨k, hk⟩
    have hm : n + 3 = 2 * (k + 2) := by omega
    have hpos : k + 2 ≠ 0 := by omega
    have shape := funext (obstructionShape_even_disc hm f)
    have bound : Integrable fun u : ℝ × ℝ => radialWeight (k + 2) (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) *
        ‖discShape (k + 2) f (discPoint u)‖ := by
      refine hint.norm.congr (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [obstructionShape_even_disc hm f u, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by unfold radialWeight; positivity)]
    rw [shape]
    exact (integral_radial_mul_doubling_holomorphic (differentiableOn_discShape (k + 2) hf)
      continuous_discRadius (fun r _ => discRadius_nonneg r) (fun r _ => discRadius_lt_one r)
      (radialWeight (k + 2)) bound (integrable_radialWeight (by omega))).trans
      (by rw [discShape_zero hpos, zero_mul])

end RadicalLie

end TernaryPeriodPolynomials.AnalyticClasses
