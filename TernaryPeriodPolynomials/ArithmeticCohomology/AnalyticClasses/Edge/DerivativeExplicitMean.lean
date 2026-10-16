module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitIntegrable

@[expose] public section


/-!
# The mean value of the closed form over the good-line coordinates

For `u = (s, t) ≠ 0` the disc coordinate of the good-line Levi point is
`w(u) = -((R - 1) / (R + 1)) (s - i t)² / (s² + t²)`: it runs twice around the circle of radius
`ψ(r) = (√(1 + r²) - 1) / (√(1 + r²) + 1)`, `r = |u|`. By the mean value property of holomorphic
functions on these circles, `∫ R^{-(n+3)} G(w(u)) Ψ(w(u)) du = G(0) Ψ(0) ∫ R^{-(n+3)} du` with
`∫ R^{-(n+3)} du = π / ((n + 3) / 2 - 1)`. The antiholomorphic term is reduced to the same form by
the reflection `t ↦ -t`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

namespace EdgeExplicit

/-! ### The angle-doubling form of the disc coordinate -/

theorem disc_identity_generic (s t a R : ℂ) (hR1 : R + 1 ≠ 0)
    (hst : s ^ 2 + t ^ 2 ≠ 0) (hE : Complex.I * (R + a ^ 2) - s * t ≠ 0)
    (ha2 : a ^ 2 = 1 + s ^ 2) (hR2 : R ^ 2 = 1 + s ^ 2 + t ^ 2) :
    (Complex.I * (R - a ^ 2) - s * t) / (Complex.I * (R + a ^ 2) - s * t) =
      -((R - 1) / (R + 1)) * ((s - t * Complex.I) ^ 2 / (s ^ 2 + t ^ 2)) := by
  field_simp
  linear_combination (Complex.I ^ 3 * R * t ^ 2 - Complex.I ^ 3 * t ^ 2 -
      2 * Complex.I ^ 2 * R * s * t + 2 * Complex.I ^ 2 * s * t - Complex.I * R * t ^ 2 -
      2 * Complex.I * s ^ 2 - Complex.I * t ^ 2) * ha2 +
    (Complex.I ^ 3 * t ^ 2 - 2 * Complex.I ^ 2 * s * t + 2 * Complex.I * s ^ 2 +
      Complex.I * t ^ 2) * hR2 +
    (Complex.I * R * s ^ 2 * t ^ 2 + Complex.I * t ^ 4 - 2 * R * s ^ 3 * t - R * s * t ^ 3 -
      s * t ^ 3) * Complex.I_sq

/-- The radius `ψ(r) = (√(1 + r²) - 1) / (√(1 + r²) + 1)` of the circle swept by `w`. -/
def discRadius (r : ℝ) : ℝ := (Real.sqrt (1 + r ^ 2) - 1) / (Real.sqrt (1 + r ^ 2) + 1)

/-- The angle-doubling disc map of `DoublingMeanValue`. -/
def doublingDisc (u : ℝ × ℝ) : ℂ :=
  -(discRadius (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) : ℂ) *
    (((u.1 : ℂ) - u.2 * Complex.I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2))

theorem sqrt_one_add_norm_sq (u : ℝ × ℝ) :
    Real.sqrt (1 + Real.sqrt (u.1 ^ 2 + u.2 ^ 2) ^ 2) = gsRadius u := by
  rw [Real.sq_sqrt (by positivity), ← add_assoc, gsRadius]

theorem complex_norm_sq_ne_zero {u : ℝ × ℝ} (hu : u ≠ 0) :
    (u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2 ≠ 0 := by
  have hpos : 0 < u.1 ^ 2 + u.2 ^ 2 := by
    rcases u with ⟨s, t⟩
    by_contra hle
    have hs : s = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    have ht : t = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    exact hu (by simp [hs, ht])
  exact_mod_cast hpos.ne'

/-- **The disc coordinate is the angle-doubling disc map** away from `0`. -/
theorem holDisc_eq_doublingDisc {u : ℝ × ℝ} (hu : u ≠ 0) : holDisc u = doublingDisc u := by
  have hR := gsRadius_pos u
  have hR1 : (gsRadius u : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : gsRadius u + 1 ≠ 0)
  rw [doublingDisc, discRadius, sqrt_one_add_norm_sq, holDisc, holE, holN]
  push_cast
  exact disc_identity_generic _ _ _ _ hR1
    (complex_norm_sq_ne_zero hu) (holE_ne_zero u) (gsAlpha_complex_sq u) (gsRadius_complex_sq u)

theorem continuous_discRadius : Continuous discRadius := by
  unfold discRadius
  refine Continuous.div (by fun_prop) (by fun_prop) fun r => ?_
  have := Real.sqrt_nonneg (1 + r ^ 2)
  linarith

theorem discRadius_nonneg {r : ℝ} : 0 ≤ discRadius r := by
  unfold discRadius
  have : 1 ≤ Real.sqrt (1 + r ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg r])
  apply div_nonneg <;> linarith

theorem discRadius_lt_one {r : ℝ} : discRadius r < 1 := by
  unfold discRadius
  have : 0 ≤ Real.sqrt (1 + r ^ 2) := Real.sqrt_nonneg _
  rw [div_lt_one (by linarith)]
  linarith

/-! ### The radial weight -/

/-- The radial weight `φ(r) = (1 + r²)^{-(n+3)/2}`. -/
def radialWeight (n : ℕ) (r : ℝ) : ℝ := (1 + r ^ 2) ^ (-(((n + 3 : ℕ) : ℝ) / 2))

theorem radialWeight_norm (u : ℝ × ℝ) :
    radialWeight n (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) =
      (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n + 3 : ℕ) : ℝ) / 2)) := by
  rw [radialWeight, Real.sq_sqrt (by positivity), ← add_assoc]

theorem radialWeight_eq_inv (u : ℝ × ℝ) :
    ((radialWeight n (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) : ℝ) : ℂ) =
      ((gsRadius u : ℂ) ^ (n + 3))⁻¹ := by
  have := norm_inv_gsRadius_pow u (n + 3)
  rw [radialWeight_norm, ← this, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (gsRadius_pos u).le]
  push_cast
  rfl

theorem radial_exponent : 1 < ((n + 3 : ℕ) : ℝ) / 2 := by
  rw [lt_div_iff₀ (by norm_num)]
  push_cast
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

theorem integrable_radialWeight :
    Integrable fun u : ℝ × ℝ => radialWeight n (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) := by
  simp only [radialWeight_norm]
  exact (integral_one_add_sq_rpow_neg radial_exponent).1

theorem integral_radialWeight :
    ∫ u : ℝ × ℝ, ((radialWeight n (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) : ℝ) : ℂ) =
      ((Real.pi / (((n + 3 : ℕ) : ℝ) / 2 - 1) : ℝ) : ℂ) := by
  rw [integral_complex_ofReal]
  simp only [radialWeight_norm]
  rw [(integral_one_add_sq_rpow_neg radial_exponent).2]

/-! ### The holomorphic factors on the unit disc -/

theorem coord_holPsi (j : Fin (n + 2)) (w : ℂ) :
    (binaryWeightBasis (n + 1)).coord j (holPsi n w) =
      ∑ m : Fin (n + 1), ((n.choose m : ℂ) * (-w) ^ (n - m)) *
        ((1 - 3 * w ^ 2) * (binaryWeightBasis (n + 1)).coord j (binaryWeightBasis (n + 1) m.succ) +
          (3 * w - w ^ 3) *
            (binaryWeightBasis (n + 1)).coord j (binaryWeightBasis (n + 1) m.castSucc)) := by
  simp only [holPsi, map_sum, map_smul, map_add, smul_eq_mul]

theorem coord_antiPsi (j : Fin (n + 2)) (w : ℂ) :
    (binaryWeightBasis (n + 1)).coord j (antiPsi n w) =
      ∑ m : Fin (n + 1), ((n.choose m : ℂ) * (-w) ^ (n - m)) *
        ((1 - 3 * w ^ 2) *
            (binaryWeightBasis (n + 1)).coord j (binaryWeightBasis (n + 1) m.rev.castSucc) +
          (3 * w - w ^ 3) *
            (binaryWeightBasis (n + 1)).coord j (binaryWeightBasis (n + 1) m.rev.succ)) := by
  simp only [antiPsi, map_sum, map_smul, map_add, smul_eq_mul]

theorem differentiable_coord_holPsi (j : Fin (n + 2)) :
    Differentiable ℂ fun w => (binaryWeightBasis (n + 1)).coord j (holPsi n w) := by
  simp only [coord_holPsi]
  exact Differentiable.fun_sum fun m _ => by fun_prop

theorem differentiable_coord_antiPsi (j : Fin (n + 2)) :
    Differentiable ℂ fun w => (binaryWeightBasis (n + 1)).coord j (antiPsi n w) := by
  simp only [coord_antiPsi]
  exact Differentiable.fun_sum fun m _ => by fun_prop

theorem exists_bound_on_closedBall {f : ℂ → ℂ} (hf : Continuous f) :
    ∃ M, ∀ w : ℂ, ‖w‖ ≤ 1 → ‖f w‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨M, fun w hw => hM w (by simpa using hw)⟩

theorem one_sub_ne_zero_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [this, norm_one] at hw
  exact lt_irrefl 1 hw

theorem diskPoint_im_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (diskPoint w).im := by
  have hne := one_sub_ne_zero_of_norm_lt hw
  have hsq : w.re ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm w
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg w]
  rw [diskPoint, Complex.div_im]
  have hpos : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hne
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  rw [← sub_div]
  apply div_pos _ hpos
  nlinarith

theorem differentiableOn_diskPoint : DifferentiableOn ℂ diskPoint (Metric.ball 0 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa using hw
  exact (((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id)
    (one_sub_ne_zero_of_norm_lt hw')).differentiableWithinAt

theorem differentiableOn_discForm {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    (h : BinaryAdelicGL) : DifferentiableOn ℂ (discForm n F h) (Metric.ball 0 1) := by
  have maps : Set.MapsTo diskPoint (Metric.ball 0 1) {z : ℂ | 0 < z.im} := fun w hw =>
    diskPoint_im_pos (by simpa using hw)
  exact ((hF.holomorphic h).comp differentiableOn_diskPoint maps).mul
    ((differentiableOn_diskPoint.add_const Complex.I).pow (n + 3))

theorem diskPoint_zero : diskPoint 0 = Complex.I := by
  simp [diskPoint]

theorem discForm_zero (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) :
    discForm n F h 0 = F h Complex.I * (2 * Complex.I) ^ (n + 3) := by
  rw [discForm, diskPoint_zero, ← two_mul]

/-! ### Integrability of the two terms of the closed form -/

theorem continuous_holDisc : Continuous holDisc :=
  continuous_holN.div continuous_holE holE_ne_zero

theorem continuous_antiDisc : Continuous antiDisc :=
  continuous_antiN.div continuous_antiE antiE_ne_zero

/-- The holomorphic term `R^{-(n+3)} G_h(w) Ψⱼ(w)` of the closed form. -/
def holTerm (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (j : Fin (n + 2))
    (u : ℝ × ℝ) : ℂ :=
  ((gsRadius u : ℂ) ^ (n + 3))⁻¹ *
    (discForm n F h (holDisc u) * (binaryWeightBasis (n + 1)).coord j (holPsi n (holDisc u)))

/-- The antiholomorphic term `R^{-(n+3)} G_{hJ}(w₂) Ψ'ⱼ(w₂)` of the closed form. -/
def antiTerm (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (j : Fin (n + 2))
    (u : ℝ × ℝ) : ℂ :=
  ((gsRadius u : ℂ) ^ (n + 3))⁻¹ *
    (discForm n F (h * atInfinity UpperHalfPlane.J) (antiDisc u) *
      (binaryWeightBasis (n + 1)).coord j (antiPsi n (antiDisc u)))

theorem continuous_inv_gsRadius_pow (k : ℕ) :
    Continuous fun u : ℝ × ℝ => ((gsRadius u : ℂ) ^ k)⁻¹ :=
  (continuous_complex_gsRadius.pow k).inv₀ fun u => pow_ne_zero k (gsRadius_complex_ne_zero u)

theorem scale_identity (u : ℝ × ℝ) (k : ℕ) :
    (gsRadius u ^ k)⁻¹ * ((gsAlpha u / Real.sqrt (gsRadius u)) ^ k *
      (3 * gsRadius u / gsAlpha u) ^ k) = 3 ^ k * (Real.sqrt (gsRadius u) ^ k)⁻¹ := by
  have ha := (gsAlpha_pos u).ne'
  have hR := (gsRadius_pos u).ne'
  have hq := (Real.sqrt_pos.mpr (gsRadius_pos u)).ne'
  rw [← mul_pow, ← inv_pow, ← inv_pow, ← mul_pow, ← mul_pow]
  congr 1
  field_simp

theorem norm_term_le {C₀ M : ℝ} (hC₀ : 0 ≤ C₀) (u : ℝ × ℝ) {Fz E c : ℂ}
    (hFz : ‖Fz‖ ≤ (gsAlpha u / Real.sqrt (gsRadius u)) ^ (n + 3) * C₀)
    (hE : ‖E‖ ≤ 3 * gsAlpha u * gsRadius u) (hc : ‖c‖ ≤ M) :
    ‖((gsRadius u : ℂ) ^ (n + 3))⁻¹ * (Fz * (E / (gsAlpha u : ℂ) ^ 2) ^ (n + 3) * c)‖ ≤
      (C₀ * M * 3 ^ (n + 3)) * (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n + 3 : ℕ) : ℝ) / 4)) := by
  have ha := gsAlpha_pos u
  have hR := gsRadius_pos u
  have hq := Real.sqrt_pos.mpr hR
  have hE' : ‖E / (gsAlpha u : ℂ) ^ 2‖ ≤ 3 * gsRadius u / gsAlpha u := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg ha.le,
      div_le_div_iff₀ (by positivity) ha]
    nlinarith
  have target : (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n + 3 : ℕ) : ℝ) / 4)) =
      (Real.sqrt (gsRadius u) ^ (n + 3))⁻¹ := by
    rw [← norm_inv_sqrt_pow, norm_inv, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hq.le]
  rw [target, norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hR.le]
  calc (gsRadius u ^ (n + 3))⁻¹ * (‖Fz‖ * ‖E / (gsAlpha u : ℂ) ^ 2‖ ^ (n + 3) * ‖c‖)
      ≤ (gsRadius u ^ (n + 3))⁻¹ * ((gsAlpha u / Real.sqrt (gsRadius u)) ^ (n + 3) * C₀ *
          (3 * gsRadius u / gsAlpha u) ^ (n + 3) * M) := by
        gcongr
    _ = C₀ * M * ((gsRadius u ^ (n + 3))⁻¹ * ((gsAlpha u / Real.sqrt (gsRadius u)) ^ (n + 3) *
          (3 * gsRadius u / gsAlpha u) ^ (n + 3))) := by ring
    _ = _ := by rw [scale_identity]; ring

theorem norm_scalar_goodPoint_le {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    {C₀ : ℝ} (hC : ∀ h, ‖F h Complex.I‖ ≤ C₀) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    ‖F h (goodPoint u)‖ ≤ (gsAlpha u / Real.sqrt (gsRadius u)) ^ (n + 3) * C₀ := by
  have hX : (((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) ^ (n + 3)) ≠ 0 := by
    rw [Complex.ofReal_div]
    exact pow_ne_zero _ (div_ne_zero (gsAlpha_complex_ne_zero u)
      (sqrt_gsRadius_complex_ne_zero u))
  have e : F h (goodPoint u) =
      ((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) ^ (n + 3) * F (movedPoint u h) Complex.I := by
    rw [eichlerData_movedPoint hF, ← mul_assoc, mul_inv_cancel₀ hX, one_mul]
  rw [e, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by
    have := gsAlpha_pos u
    have := Real.sqrt_pos.mpr (gsRadius_pos u)
    positivity)]
  exact mul_le_mul_of_nonneg_left (hC _)
    (pow_nonneg (div_nonneg (gsAlpha_pos u).le (Real.sqrt_nonneg _)) _)

theorem norm_scalar_reflection_le {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    {C₀ : ℝ} (hC : ∀ h, ‖F h Complex.I‖ ≤ C₀) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    ‖F (h * atInfinity UpperHalfPlane.J) (binaryComplexReflection (goodPoint u))‖ ≤
      (gsAlpha u / Real.sqrt (gsRadius u)) ^ (n + 3) * C₀ := by
  have hX : (((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) ^ (n + 3)) ≠ 0 := by
    rw [Complex.ofReal_div]
    exact pow_ne_zero _ (div_ne_zero (gsAlpha_complex_ne_zero u)
      (sqrt_gsRadius_complex_ne_zero u))
  have e : F (h * atInfinity UpperHalfPlane.J) (binaryComplexReflection (goodPoint u)) =
      ((gsAlpha u / Real.sqrt (gsRadius u) : ℝ) : ℂ) ^ (n + 3) *
        F (movedPoint u h * atInfinity UpperHalfPlane.J) Complex.I := by
    rw [eichlerData_movedPoint_J hF, ← mul_assoc, mul_inv_cancel₀ hX, one_mul]
  rw [e, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by
    have := gsAlpha_pos u
    have := Real.sqrt_pos.mpr (gsRadius_pos u)
    positivity)]
  exact mul_le_mul_of_nonneg_left (hC _)
    (pow_nonneg (div_nonneg (gsAlpha_pos u).le (Real.sqrt_nonneg _)) _)

theorem integrable_holTerm {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    (large : 2 ≤ n) (h : BinaryAdelicGL) (j : Fin (n + 2)) : Integrable (holTerm n F h j) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_bound_at_I hF
  obtain ⟨M, hM⟩ := exists_bound_on_closedBall (differentiable_coord_holPsi (n := n) j).continuous
  have continuity : Continuous (holTerm n F h j) := by
    have e : holTerm n F h j = fun u => ((gsRadius u : ℂ) ^ (n + 3))⁻¹ *
        (F h (goodPoint u) * (holE u / (gsAlpha u : ℂ) ^ 2) ^ (n + 3) *
          (binaryWeightBasis (n + 1)).coord j (holPsi n (holDisc u))) := by
      funext u
      rw [holTerm, discForm_holDisc]
    rw [e]
    exact (continuous_inv_gsRadius_pow _).mul (((continuous_scalar_goodPoint hF h).mul
      ((continuous_holE.div (continuous_complex_gsAlpha.pow 2) fun u =>
        pow_ne_zero 2 (gsAlpha_complex_ne_zero u)).pow _)).mul
      ((differentiable_coord_holPsi j).continuous.comp continuous_holDisc))
  refine integrable_of_continuous_decay continuity (decay_exponent large)
    (C := C₀ * M * 3 ^ (n + 3)) fun u => ?_
  rw [holTerm, discForm_holDisc]
  exact norm_term_le hC₀ u
    (norm_scalar_goodPoint_le hF hC u h) (norm_holE_le u) (hM _ (norm_holDisc_lt_one u).le)

theorem integrable_antiTerm {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    (large : 2 ≤ n) (h : BinaryAdelicGL) (j : Fin (n + 2)) : Integrable (antiTerm n F h j) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_bound_at_I hF
  obtain ⟨M, hM⟩ := exists_bound_on_closedBall
    (differentiable_coord_antiPsi (n := n) j).continuous
  have continuity : Continuous (antiTerm n F h j) := by
    have e : antiTerm n F h j = fun u => ((gsRadius u : ℂ) ^ (n + 3))⁻¹ *
        (F (h * atInfinity UpperHalfPlane.J) (binaryComplexReflection (goodPoint u)) *
          (antiE u / (gsAlpha u : ℂ) ^ 2) ^ (n + 3) *
          (binaryWeightBasis (n + 1)).coord j (antiPsi n (antiDisc u))) := by
      funext u
      rw [antiTerm, discForm_antiDisc]
    rw [e]
    exact (continuous_inv_gsRadius_pow _).mul (((continuous_scalar_reflection hF _).mul
      ((continuous_antiE.div (continuous_complex_gsAlpha.pow 2) fun u =>
        pow_ne_zero 2 (gsAlpha_complex_ne_zero u)).pow _)).mul
      ((differentiable_coord_antiPsi j).continuous.comp continuous_antiDisc))
  refine integrable_of_continuous_decay continuity (decay_exponent large)
    (C := C₀ * M * 3 ^ (n + 3)) fun u => ?_
  rw [antiTerm, discForm_antiDisc]
  exact norm_term_le hC₀ u
    (norm_scalar_reflection_le hF hC u h) (norm_antiE_le u) (hM _ (norm_antiDisc_lt_one u).le)

/-! ### The mean value -/

theorem radialWeight_nonneg (r : ℝ) : 0 ≤ radialWeight n r :=
  Real.rpow_nonneg (by positivity) _

theorem integral_mean_value {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (Metric.ball 0 1))
    {g : ℝ × ℝ → ℂ} (hg : Integrable g)
    (hgG : ∀ u : ℝ × ℝ, u ≠ 0 → g u = ((gsRadius u : ℂ) ^ (n + 3))⁻¹ * G (holDisc u)) :
    ∫ u, g u = G 0 * ((Real.pi / (((n + 3 : ℕ) : ℝ) / 2 - 1) : ℝ) : ℂ) := by
  have ae : ∀ᵐ u ∂(volume : Measure (ℝ × ℝ)), g u =
      ((radialWeight n (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) : ℝ) : ℂ) *
        G (-(discRadius (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) : ℂ) *
          (((u.1 : ℂ) - u.2 * Complex.I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2))) := by
    filter_upwards [Measure.ae_ne volume 0] with u hu
    rw [hgG u hu, radialWeight_eq_inv, holDisc_eq_doublingDisc hu]
    rfl
  have hint : Integrable fun u : ℝ × ℝ => radialWeight n (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) *
      ‖G (-(discRadius (Real.sqrt (u.1 ^ 2 + u.2 ^ 2)) : ℂ) *
        (((u.1 : ℂ) - u.2 * Complex.I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2)))‖ := by
    refine hg.norm.congr ?_
    filter_upwards [ae] with u hu
    rw [hu, norm_mul, Complex.norm_real, Real.norm_of_nonneg (radialWeight_nonneg _)]
  rw [integral_congr_ae ae, integral_radial_mul_doubling_holomorphic hG continuous_discRadius
    (fun _ _ => discRadius_nonneg) (fun _ _ => discRadius_lt_one) (radialWeight n) hint
    integrable_radialWeight, integral_radialWeight]

/-- **The mean value of the holomorphic term.** -/
theorem integral_holTerm {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F) (large : 2 ≤ n)
    (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    ∫ u, holTerm n F h j u = discForm n F h 0 *
      (binaryWeightBasis (n + 1)).coord j (holPsi n 0) *
        ((Real.pi / (((n + 3 : ℕ) : ℝ) / 2 - 1) : ℝ) : ℂ) :=
  integral_mean_value ((differentiableOn_discForm hF h).mul
    (differentiable_coord_holPsi j).differentiableOn) (integrable_holTerm hF large h j)
    fun _ _ => rfl

/-! ### The reflection `t ↦ -t` -/

theorem gsRadius_reflect (u : ℝ × ℝ) : gsRadius (u.1, -u.2) = gsRadius u := by
  simp [gsRadius]

theorem gsAlpha_reflect (u : ℝ × ℝ) : gsAlpha (u.1, -u.2) = gsAlpha u := rfl

theorem holDisc_reflect (u : ℝ × ℝ) : holDisc (u.1, -u.2) = antiDisc u := by
  simp only [holDisc, holN, holE, antiDisc, antiN, antiE, gsRadius_reflect, gsAlpha_reflect]
  push_cast
  ring_nf

theorem measurePreserving_reflect :
    MeasurePreserving (Prod.map id (fun t : ℝ => -t)) (volume : Measure (ℝ × ℝ)) volume :=
  (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)

/-- The reflection `(s, t) ↦ (s, -t)` as a measurable equivalence. -/
def reflectEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)

theorem integral_reflect (g : ℝ × ℝ → ℂ) : ∫ u : ℝ × ℝ, g (u.1, -u.2) = ∫ u, g u := by
  have := measurePreserving_reflect.integral_comp reflectEquiv.measurableEmbedding g
  simpa [Prod.map] using this

theorem integrable_reflect_iff (g : ℝ × ℝ → ℂ) :
    Integrable (fun u : ℝ × ℝ => g (u.1, -u.2)) ↔ Integrable g := by
  have := measurePreserving_reflect.integrable_comp_emb reflectEquiv.measurableEmbedding (g := g)
  simpa [Function.comp_def, Prod.map] using this

/-- The reflected antiholomorphic term `R^{-(n+3)} G_{hJ}(w) Ψ'ⱼ(w)` at the disc coordinate
`w = holDisc u`. -/
def reflectedTerm (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (j : Fin (n + 2))
    (u : ℝ × ℝ) : ℂ :=
  ((gsRadius u : ℂ) ^ (n + 3))⁻¹ *
    (discForm n F (h * atInfinity UpperHalfPlane.J) (holDisc u) *
      (binaryWeightBasis (n + 1)).coord j (antiPsi n (holDisc u)))

theorem antiTerm_eq_reflectedTerm (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) (u : ℝ × ℝ) : antiTerm n F h j u = reflectedTerm n F h j (u.1, -u.2) := by
  rw [antiTerm, reflectedTerm, gsRadius_reflect, holDisc_reflect]

/-- **The mean value of the antiholomorphic term.** -/
theorem integral_antiTerm {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F) (large : 2 ≤ n)
    (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    ∫ u, antiTerm n F h j u = discForm n F (h * atInfinity UpperHalfPlane.J) 0 *
      (binaryWeightBasis (n + 1)).coord j (antiPsi n 0) *
        ((Real.pi / (((n + 3 : ℕ) : ℝ) / 2 - 1) : ℝ) : ℂ) := by
  have reflected : Integrable (reflectedTerm n F h j) := by
    rw [← integrable_reflect_iff]
    refine (integrable_antiTerm hF large h j).congr (Filter.Eventually.of_forall fun _ => ?_)
    rw [antiTerm_eq_reflectedTerm]
  simp only [antiTerm_eq_reflectedTerm]
  rw [integral_reflect (reflectedTerm n F h j)]
  exact integral_mean_value ((differentiableOn_discForm hF _).mul
    (differentiable_coord_antiPsi j).differentiableOn) reflected fun _ _ => rfl

end EdgeExplicit

end TernaryPeriodPolynomials.AnalyticClasses
