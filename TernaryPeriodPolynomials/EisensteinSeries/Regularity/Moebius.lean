module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


/-!
# Möbius algebra on `ℂ ∖ ℝ`

For a real invertible matrix `g` the map `w ↦ (a w + b) / (c w + d)` permutes `ℂ ∖ ℝ`
(and `{Im > 0}` when `det g > 0`).  This file develops the algebra of that action:
the cocycle `denom (g h) w = denom g (h w) * denom h w`, the imaginary part formula, holomorphy,
the weight-`k` automorphy factor `autFactor`, the identity `g * gBar w = gBar (g w) * stab`, and
the rotations `rotGL θ` together with their action on the Cayley transform.
-/

noncomputable section

open scoped Matrix

namespace TernaryPeriodPolynomials.Regularity

/-! ### Membership and matrix entries -/

theorem mem_offReal_iff {w : ℂ} : w ∈ offReal ↔ w.im ≠ 0 := Iff.rfl

theorem mem_upper_iff {z : ℂ} : z ∈ upper ↔ 0 < z.im := Iff.rfl

theorem gl_det_ne_zero (g : GL (Fin 2) ℝ) : g.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det g.val).1 g.isUnit).ne_zero

theorem gl_det_eq (g : GL (Fin 2) ℝ) :
    g.val.det = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 :=
  Matrix.det_fin_two g.val

theorem gl_det_mul (g h : GL (Fin 2) ℝ) : (g * h).val.det = g.val.det * h.val.det := by
  rw [Units.val_mul, Matrix.det_mul]

theorem gl_det_inv (g : GL (Fin 2) ℝ) : (g⁻¹).val.det = (g.val.det)⁻¹ := by
  have h : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← gl_det_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  exact eq_inv_of_mul_eq_one_right h

theorem gl_mul_apply (g h : GL (Fin 2) ℝ) (i j : Fin 2) :
    (g * h).val i j = g.val i 0 * h.val 0 j + g.val i 1 * h.val 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem gl_ext {g h : GL (Fin 2) ℝ} (h00 : g.val 0 0 = h.val 0 0) (h01 : g.val 0 1 = h.val 0 1)
    (h10 : g.val 1 0 = h.val 1 0) (h11 : g.val 1 1 = h.val 1 1) : g = h := by
  apply Units.ext
  rw [Matrix.eta_fin_two g.val, Matrix.eta_fin_two h.val, h00, h01, h10, h11]

theorem gl_one_00 : (1 : GL (Fin 2) ℝ).val 0 0 = 1 := by simp

theorem gl_one_01 : (1 : GL (Fin 2) ℝ).val 0 1 = 0 := by simp

theorem gl_one_10 : (1 : GL (Fin 2) ℝ).val 1 0 = 0 := by simp

theorem gl_one_11 : (1 : GL (Fin 2) ℝ).val 1 1 = 1 := by simp

theorem gUp_00 {z : ℂ} (h : z.im ≠ 0) : (gUp z).val 0 0 = z.im := by rw [gUp_val h]; simp

theorem gUp_01 {z : ℂ} (h : z.im ≠ 0) : (gUp z).val 0 1 = z.re := by rw [gUp_val h]; simp

theorem gUp_10 {z : ℂ} (h : z.im ≠ 0) : (gUp z).val 1 0 = 0 := by rw [gUp_val h]; simp

theorem gUp_11 {z : ℂ} (h : z.im ≠ 0) : (gUp z).val 1 1 = 1 := by rw [gUp_val h]; simp

theorem gBar_00 {w : ℂ} (h : w.im ≠ 0) : (gBar w).val 0 0 = -w.im := by rw [gBar_val h]; simp

theorem gBar_01 {w : ℂ} (h : w.im ≠ 0) : (gBar w).val 0 1 = w.re := by rw [gBar_val h]; simp

theorem gBar_10 {w : ℂ} (h : w.im ≠ 0) : (gBar w).val 1 0 = 0 := by rw [gBar_val h]; simp

theorem gBar_11 {w : ℂ} (h : w.im ≠ 0) : (gBar w).val 1 1 = 1 := by rw [gBar_val h]; simp

theorem stab_00 {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : (stab a b).val 0 0 = a := by
  rw [stab_val h]; simp

theorem stab_01 {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : (stab a b).val 0 1 = b := by
  rw [stab_val h]; simp

theorem stab_10 {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : (stab a b).val 1 0 = -b := by
  rw [stab_val h]; simp

theorem stab_11 {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : (stab a b).val 1 1 = a := by
  rw [stab_val h]; simp

theorem rotGL_00 (θ : ℝ) : (rotGL θ).val 0 0 = Real.cos θ := by rw [rotGL_val]; simp

theorem rotGL_01 (θ : ℝ) : (rotGL θ).val 0 1 = -Real.sin θ := by rw [rotGL_val]; simp

theorem rotGL_10 (θ : ℝ) : (rotGL θ).val 1 0 = Real.sin θ := by rw [rotGL_val]; simp

theorem rotGL_11 (θ : ℝ) : (rotGL θ).val 1 1 = Real.cos θ := by rw [rotGL_val]; simp

/-! ### The action on `ℂ ∖ ℝ` -/

theorem denom_def (g : GL (Fin 2) ℝ) (w : ℂ) :
    denom g w = (g.val 1 0 : ℂ) * w + (g.val 1 1 : ℂ) := rfl

theorem moeb_def (g : GL (Fin 2) ℝ) (w : ℂ) :
    moeb g w = ((g.val 0 0 : ℂ) * w + (g.val 0 1 : ℂ)) / denom g w := rfl

theorem denom_re (g : GL (Fin 2) ℝ) (w : ℂ) :
    (denom g w).re = g.val 1 0 * w.re + g.val 1 1 := by
  simp [denom_def]

theorem denom_im (g : GL (Fin 2) ℝ) (w : ℂ) : (denom g w).im = g.val 1 0 * w.im := by
  simp [denom_def]

/-- The automorphy factor `c w + d` does not vanish off the real axis. -/
theorem denom_ne_zero (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) : denom g w ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  rw [denom_im, Complex.zero_im] at him
  rw [denom_re, Complex.zero_re] at hre
  have hc : g.val 1 0 = 0 := (mul_eq_zero.1 him).resolve_right hw
  rw [hc, zero_mul, zero_add] at hre
  apply gl_det_ne_zero g
  rw [gl_det_eq, hc, hre]
  ring

/-- The imaginary part of `moeb g w`. -/
theorem im_moeb (g : GL (Fin 2) ℝ) (w : ℂ) :
    (moeb g w).im = g.val.det * w.im / Complex.normSq (denom g w) := by
  rw [moeb_def, Complex.div_im, denom_re, denom_im, gl_det_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.mul_re]
  ring

theorem moeb_im_ne_zero (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) : (moeb g w).im ≠ 0 := by
  rw [im_moeb]
  exact div_ne_zero (mul_ne_zero (gl_det_ne_zero g) hw)
    (Complex.normSq_pos.2 (denom_ne_zero g hw)).ne'

theorem moeb_mem_offReal (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w ∈ offReal) : moeb g w ∈ offReal :=
  mem_offReal_iff.2 (moeb_im_ne_zero g (mem_offReal_iff.1 hw))

theorem moeb_mem_upper (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) {z : ℂ} (hz : z ∈ upper) :
    moeb g z ∈ upper := by
  have hz' : 0 < z.im := mem_upper_iff.1 hz
  refine mem_upper_iff.2 ?_
  rw [im_moeb]
  exact div_pos (mul_pos hg hz') (Complex.normSq_pos.2 (denom_ne_zero g hz'.ne'))

theorem moeb_mul_denom {g : GL (Fin 2) ℝ} {w : ℂ} (hw : denom g w ≠ 0) :
    moeb g w * denom g w = (g.val 0 0 : ℂ) * w + (g.val 0 1 : ℂ) := by
  rw [moeb_def]
  exact div_mul_cancel₀ _ hw

/-- The cocycle relation for the automorphy factor. -/
theorem denom_mul (g h : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    denom (g * h) w = denom g (moeb h w) * denom h w := by
  have hm := moeb_mul_denom (denom_ne_zero h hw)
  have key : denom g (moeb h w) * denom h w
      = (g.val 1 0 : ℂ) * (moeb h w * denom h w) + (g.val 1 1 : ℂ) * denom h w := by
    rw [denom_def g (moeb h w)]
    ring
  rw [key, hm]
  simp only [denom_def, gl_mul_apply]
  push_cast
  ring

/-- `moeb` is an action of `GL₂(ℝ)`. -/
theorem moeb_mul (g h : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    moeb (g * h) w = moeb g (moeb h w) := by
  have hD := denom_ne_zero h hw
  have hm := moeb_mul_denom hD
  have hn : ((g * h).val 0 0 : ℂ) * w + ((g * h).val 0 1 : ℂ)
      = ((g.val 0 0 : ℂ) * moeb h w + (g.val 0 1 : ℂ)) * denom h w := by
    have key : ((g.val 0 0 : ℂ) * moeb h w + (g.val 0 1 : ℂ)) * denom h w
        = (g.val 0 0 : ℂ) * (moeb h w * denom h w) + (g.val 0 1 : ℂ) * denom h w := by ring
    rw [key, hm]
    simp only [denom_def, gl_mul_apply]
    push_cast
    ring
  rw [moeb_def (g * h) w, moeb_def g (moeb h w), hn, denom_mul g h hw]
  exact mul_div_mul_right _ _ hD

theorem denom_one (w : ℂ) : denom 1 w = 1 := by
  rw [denom_def, gl_one_10, gl_one_11]
  simp

theorem moeb_one (w : ℂ) : moeb 1 w = w := by
  rw [moeb_def, denom_one, gl_one_00, gl_one_01]
  simp

theorem moeb_inv_moeb (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    moeb g⁻¹ (moeb g w) = w := by
  rw [← moeb_mul g⁻¹ g hw, inv_mul_cancel, moeb_one]

theorem moeb_moeb_inv (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    moeb g (moeb g⁻¹ w) = w := by
  rw [← moeb_mul g g⁻¹ hw, mul_inv_cancel, moeb_one]

theorem denom_inv_moeb (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    denom g⁻¹ (moeb g w) * denom g w = 1 := by
  rw [← denom_mul g⁻¹ g hw, inv_mul_cancel, denom_one]

theorem moeb_injOn (g : GL (Fin 2) ℝ) : Set.InjOn (moeb g) offReal := by
  intro x hx y hy hxy
  have h := congrArg (moeb g⁻¹) hxy
  rwa [moeb_inv_moeb g (mem_offReal_iff.1 hx), moeb_inv_moeb g (mem_offReal_iff.1 hy)] at h

theorem moeb_image_offReal (g : GL (Fin 2) ℝ) : moeb g '' offReal = offReal := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact moeb_mem_offReal g hx
  · intro hw
    exact ⟨moeb g⁻¹ w, moeb_mem_offReal _ hw, moeb_moeb_inv g (mem_offReal_iff.1 hw)⟩

/-! ### Conjugation and rotations by `-θ` -/

theorem denom_conj (g : GL (Fin 2) ℝ) (w : ℂ) :
    denom g ((starRingEnd ℂ) w) = (starRingEnd ℂ) (denom g w) := by
  simp [denom_def]

theorem moeb_conj (g : GL (Fin 2) ℝ) (w : ℂ) :
    moeb g ((starRingEnd ℂ) w) = (starRingEnd ℂ) (moeb g w) := by
  simp only [moeb_def, denom_conj, map_div₀, map_add, map_mul, Complex.conj_ofReal]

theorem denom_rotGL (θ : ℝ) (w : ℂ) : denom (rotGL θ) w = Real.sin θ * w + Real.cos θ := by
  rw [denom_def, rotGL_10, rotGL_11]

theorem denom_rotGL_neg (θ : ℝ) (w : ℂ) :
    denom (rotGL (-θ)) (-w) = denom (rotGL θ) w := by
  rw [denom_rotGL, denom_rotGL, Real.sin_neg, Real.cos_neg, Complex.ofReal_neg]
  ring

theorem moeb_rotGL_neg (θ : ℝ) (w : ℂ) :
    moeb (rotGL (-θ)) (-w) = -moeb (rotGL θ) w := by
  rw [moeb_def, moeb_def, denom_rotGL_neg θ w]
  simp only [rotGL_00, rotGL_01, Real.cos_neg, Real.sin_neg, neg_neg, Complex.ofReal_neg]
  ring

/-! ### Holomorphy and measurability -/

/-- The derivative of the Möbius transformation `moeb g` off the real axis. -/
theorem hasDerivAt_moeb (g : GL (Fin 2) ℝ) {w : ℂ} (hw : denom g w ≠ 0) :
    HasDerivAt (moeb g) ((g.val.det : ℂ) / denom g w ^ 2) w := by
  have h1 : HasDerivAt (fun y : ℂ => (g.val 0 0 : ℂ) * y + (g.val 0 1 : ℂ)) (g.val 0 0 : ℂ) w := by
    simpa using ((hasDerivAt_id' w).const_mul (g.val 0 0 : ℂ)).add_const (g.val 0 1 : ℂ)
  have h2 : HasDerivAt (fun y : ℂ => (g.val 1 0 : ℂ) * y + (g.val 1 1 : ℂ)) (g.val 1 0 : ℂ) w := by
    simpa using ((hasDerivAt_id' w).const_mul (g.val 1 0 : ℂ)).add_const (g.val 1 1 : ℂ)
  refine (h1.fun_div h2 hw).congr_deriv ?_
  simp only [gl_det_eq, denom_def]
  push_cast
  ring

theorem differentiable_denom (g : GL (Fin 2) ℝ) : Differentiable ℂ (denom g) := by
  show Differentiable ℂ fun w : ℂ => (g.val 1 0 : ℂ) * w + (g.val 1 1 : ℂ)
  fun_prop

theorem differentiableOn_moeb (g : GL (Fin 2) ℝ) : DifferentiableOn ℂ (moeb g) offReal :=
  fun _ hw =>
    (hasDerivAt_moeb g (denom_ne_zero g (mem_offReal_iff.1 hw))).differentiableAt
      |>.differentiableWithinAt

theorem continuousOn_moeb (g : GL (Fin 2) ℝ) : ContinuousOn (moeb g) offReal :=
  (differentiableOn_moeb g).continuousOn

theorem measurable_moeb (g : GL (Fin 2) ℝ) : Measurable (moeb g) := by
  have hN : Measurable fun w : ℂ => (g.val 0 0 : ℂ) * w + (g.val 0 1 : ℂ) := by fun_prop
  have hD : Measurable (denom g) := (differentiable_denom g).continuous.measurable
  exact hN.div hD

/-! ### The weight-`k` automorphy factor -/

theorem autFactor_mul (k : ℕ) (g h : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    autFactor k (g * h) w = autFactor k g w * autFactor k h (moeb g⁻¹ w) := by
  have hmul : (|(g * h).val.det| ^ ((k : ℝ) / 2))⁻¹
      = (|g.val.det| ^ ((k : ℝ) / 2))⁻¹ * (|h.val.det| ^ ((k : ℝ) / 2))⁻¹ := by
    rw [gl_det_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_inv]
  unfold autFactor
  rw [hmul, mul_inv_rev g h, denom_mul h⁻¹ g⁻¹ hw, Complex.ofReal_mul, mul_pow, mul_inv]
  ring

theorem autFactor_one (k : ℕ) (w : ℂ) : autFactor k 1 w = 1 := by
  simp [autFactor, denom_one]

theorem autFactor_ne_zero (k : ℕ) (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    autFactor k g w ≠ 0 := by
  have hδ : 0 < |g.val.det| := abs_pos.2 (gl_det_ne_zero g)
  unfold autFactor
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.rpow_pos_of_pos hδ _).ne'))
    (inv_ne_zero (pow_ne_zero _ (denom_ne_zero _ hw)))

theorem rpow_half_sq {y : ℝ} (hy : 0 < y) (k : ℕ) : (y ^ ((k : ℝ) / 2)) ^ 2 = y ^ k := by
  have h : (k : ℝ) / 2 + (k : ℝ) / 2 = (k : ℝ) := by ring
  rw [sq, ← Real.rpow_add hy, h, Real.rpow_natCast]

/-- The squared norm of the automorphy factor, in terms of the imaginary part of `g⁻¹ w`. -/
theorem norm_autFactor_sq (k : ℕ) (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    ‖autFactor k g w‖ ^ 2 * |w.im| ^ k = |(moeb g⁻¹ w).im| ^ k := by
  have hδ : 0 < |g.val.det| := abs_pos.2 (gl_det_ne_zero g)
  have hD : denom g⁻¹ w ≠ 0 := denom_ne_zero _ hw
  have hn : 0 < Complex.normSq (denom g⁻¹ w) := Complex.normSq_pos.2 hD
  have hA : ((|g.val.det| ^ ((k : ℝ) / 2))⁻¹) ^ 2 = (|g.val.det| ^ k)⁻¹ := by
    rw [inv_pow, rpow_half_sq hδ]
  have hb : (‖denom g⁻¹ w‖ ^ k) ^ 2 = Complex.normSq (denom g⁻¹ w) ^ k := by
    rw [← Complex.sq_norm]
    ring
  have hnorm : ‖autFactor k g w‖ ^ 2
      = (|g.val.det| ^ k)⁻¹ * (Complex.normSq (denom g⁻¹ w) ^ k)⁻¹ := by
    rw [autFactor, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, _root_.sq_abs, hA,
      norm_inv, norm_pow, inv_pow, hb]
  have habs : |(moeb g⁻¹ w).im| = (|g.val.det|)⁻¹ * |w.im| / Complex.normSq (denom g⁻¹ w) := by
    rw [im_moeb, gl_det_inv, abs_div, abs_mul, abs_inv, abs_of_pos hn]
  rw [hnorm, habs, div_pow, mul_pow, inv_pow]
  ring

/-- The fractional-power form of `norm_autFactor_sq`. -/
theorem norm_autFactor_rpow (k : ℕ) (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    ‖autFactor k g w‖ * |w.im| ^ ((k : ℝ) / 2) = |(moeb g⁻¹ w).im| ^ ((k : ℝ) / 2) := by
  have hx : 0 < |w.im| := abs_pos.2 hw
  have hm : 0 < |(moeb g⁻¹ w).im| := abs_pos.2 (moeb_im_ne_zero _ hw)
  have h : (‖autFactor k g w‖ * |w.im| ^ ((k : ℝ) / 2)) ^ 2
      = (|(moeb g⁻¹ w).im| ^ ((k : ℝ) / 2)) ^ 2 := by
    rw [mul_pow, rpow_half_sq hx, rpow_half_sq hm]
    exact norm_autFactor_sq k g hw
  exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 h

theorem differentiableOn_autFactor (k : ℕ) (g : GL (Fin 2) ℝ) :
    DifferentiableOn ℂ (autFactor k g) offReal := by
  intro w hw
  have hD := denom_ne_zero g⁻¹ (mem_offReal_iff.1 hw)
  have h1 : DifferentiableAt ℂ (fun y => denom g⁻¹ y ^ k) w :=
    ((differentiable_denom g⁻¹) w).pow k
  have h2 := (h1.inv (pow_ne_zero k hD)).const_mul
    (((|g.val.det| ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ)
  exact h2.differentiableWithinAt

theorem continuousOn_autFactor (k : ℕ) (g : GL (Fin 2) ℝ) :
    ContinuousOn (autFactor k g) offReal :=
  (differentiableOn_autFactor k g).continuousOn

theorem measurable_autFactor (k : ℕ) (g : GL (Fin 2) ℝ) : Measurable (autFactor k g) := by
  have h : Measurable (denom g⁻¹) := (differentiable_denom g⁻¹).continuous.measurable
  show Measurable fun w : ℂ =>
    (((|g.val.det| ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) * (denom g⁻¹ w ^ k)⁻¹
  exact ((h.pow_const k).inv).const_mul _

/-! ### The matrices `gUp` and `gBar` -/

theorem denom_gUp {z : ℂ} (hz : z.im ≠ 0) (w : ℂ) : denom (gUp z) w = 1 := by
  rw [denom_def, gUp_10 hz, gUp_11 hz]
  simp

theorem moeb_gUp_I {z : ℂ} (hz : z.im ≠ 0) : moeb (gUp z) Complex.I = z := by
  rw [moeb_def, denom_gUp hz, gUp_00 hz, gUp_01 hz, div_one]
  exact (add_comm _ _).trans z.re_add_im

theorem moeb_gBar_I {w : ℂ} (hw : w.im ≠ 0) :
    moeb (gBar w) Complex.I = (starRingEnd ℂ) w :=
  moeb_gUp_I (z := (starRingEnd ℂ) w) (by simpa using hw)

theorem moeb_gBar_neg_I {w : ℂ} (hw : w.im ≠ 0) : moeb (gBar w) (-Complex.I) = w := by
  have hz : ((starRingEnd ℂ) w).im ≠ 0 := by simpa using hw
  have hd : denom (gBar w) (-Complex.I) = 1 := denom_gUp hz _
  rw [moeb_def, hd, gBar_00 hw, gBar_01 hw, div_one]
  have h : ((-w.im : ℝ) : ℂ) * -Complex.I + (w.re : ℂ) = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact w.re_add_im

theorem gUp_I : gUp Complex.I = 1 := by
  have hI : Complex.I.im ≠ 0 := by simp
  apply gl_ext
  · rw [gUp_00 hI, gl_one_00]
    simp
  · rw [gUp_01 hI, gl_one_01]
    simp
  · rw [gUp_10 hI, gl_one_10]
  · rw [gUp_11 hI, gl_one_11]

theorem stab_sq_ne (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    (denom g w).re ^ 2 + (denom g w).im ^ 2 ≠ 0 := by
  have h := Complex.normSq_pos.2 (denom_ne_zero g hw)
  rw [Complex.normSq_apply] at h
  intro h'
  nlinarith

/-- The key identity `g * gBar w = gBar (g w) * stab (Re (c w + d)) (Im (c w + d))`. -/
theorem mul_gBar (g : GL (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    g * gBar w = gBar (moeb g w) * stab (denom g w).re (denom g w).im := by
  have hm' : (moeb g w).im ≠ 0 := moeb_im_ne_zero g hw
  have hs := stab_sq_ne g hw
  have hm := moeb_mul_denom (denom_ne_zero g hw)
  have hre : (moeb g w).re * (denom g w).re - (moeb g w).im * (denom g w).im
      = g.val 0 0 * w.re + g.val 0 1 := by
    have h := congrArg Complex.re hm
    rw [Complex.mul_re] at h
    simpa using h
  have him : (moeb g w).re * (denom g w).im + (moeb g w).im * (denom g w).re
      = g.val 0 0 * w.im := by
    have h := congrArg Complex.im hm
    rw [Complex.mul_im] at h
    simpa using h
  have hp := denom_re g w
  have hq := denom_im g w
  apply gl_ext
  · simp only [gl_mul_apply, gBar_00 hw, gBar_10 hw, gBar_00 hm', gBar_01 hm', stab_00 hs,
      stab_10 hs]
    linear_combination him
  · simp only [gl_mul_apply, gBar_01 hw, gBar_11 hw, gBar_00 hm', gBar_01 hm', stab_01 hs,
      stab_11 hs]
    linear_combination (-1 : ℝ) * hre
  · simp only [gl_mul_apply, gBar_00 hw, gBar_10 hw, gBar_10 hm', gBar_11 hm', stab_00 hs,
      stab_10 hs]
    linear_combination hq
  · simp only [gl_mul_apply, gBar_01 hw, gBar_11 hw, gBar_10 hm', gBar_11 hm', stab_01 hs,
      stab_11 hs]
    linear_combination (-1 : ℝ) * hp

/-! ### Rotations -/

theorem rotGL_zero : rotGL 0 = 1 := by
  apply gl_ext <;>
    simp [rotGL_00, rotGL_01, rotGL_10, rotGL_11, gl_one_00, gl_one_01, gl_one_10, gl_one_11]

theorem rotGL_add (θ φ : ℝ) : rotGL (θ + φ) = rotGL θ * rotGL φ := by
  apply gl_ext <;>
    simp only [gl_mul_apply, rotGL_00, rotGL_01, rotGL_10, rotGL_11, Real.cos_add,
      Real.sin_add] <;>
    ring

theorem rotGL_neg (θ : ℝ) : rotGL (-θ) = (rotGL θ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rotGL_add, neg_add_cancel, rotGL_zero]

theorem det_rotGL (θ : ℝ) : (rotGL θ).val.det = 1 := by
  rw [gl_det_eq, rotGL_00, rotGL_01, rotGL_10, rotGL_11]
  linear_combination Real.cos_sq_add_sin_sq θ

theorem denom_rotGL_I (θ : ℝ) : denom (rotGL θ) Complex.I = Complex.exp (θ * Complex.I) := by
  rw [denom_rotGL, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem moeb_rotGL_I (θ : ℝ) : moeb (rotGL θ) Complex.I = Complex.I := by
  rw [moeb_def, denom_rotGL_I, div_eq_iff (Complex.exp_ne_zero _), rotGL_00, rotGL_01,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_neg]
  linear_combination (-(Real.sin θ : ℂ)) * Complex.I_sq

theorem denom_rotGL_mul_add_I (θ : ℝ) {w : ℂ} (hw : denom (rotGL θ) w ≠ 0) :
    denom (rotGL θ) w * (moeb (rotGL θ) w + Complex.I)
      = Complex.exp (θ * Complex.I) * (w + Complex.I) := by
  have hm := moeb_mul_denom hw
  have hD := denom_rotGL θ w
  rw [rotGL_00, rotGL_01, Complex.ofReal_neg] at hm
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  linear_combination hm + Complex.I * hD + (-(Real.sin θ : ℂ)) * Complex.I_sq

/-- The rotation `rotGL θ` acts on the Cayley transform by multiplication by `e^{-2iθ}`. -/
theorem cay_moeb_rotGL (θ : ℝ) {z : ℂ} (hz : 0 < z.im) :
    cay (moeb (rotGL θ) z) = Complex.exp (-(2 * θ) * Complex.I) * cay z := by
  have hD : denom (rotGL θ) z ≠ 0 := denom_ne_zero _ hz.ne'
  have hb := denom_rotGL_mul_add_I θ hD
  have hm := moeb_mul_denom hD
  have hDz := denom_rotGL θ z
  rw [rotGL_00, rotGL_01, Complex.ofReal_neg] at hm
  have ha : denom (rotGL θ) z * (moeb (rotGL θ) z - Complex.I)
      = Complex.exp (-(θ : ℂ) * Complex.I) * (z - Complex.I) := by
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    linear_combination hm - Complex.I * hDz + (-(Real.sin θ : ℂ)) * Complex.I_sq
  have hexp : Complex.exp (-(2 * θ) * Complex.I)
      = Complex.exp (-(θ : ℂ) * Complex.I) / Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_sub]
    congr 1
    ring
  rw [cay, cay, hexp,
    ← mul_div_mul_left (moeb (rotGL θ) z - Complex.I) (moeb (rotGL θ) z + Complex.I) hD, ha, hb,
    div_mul_div_comm]

theorem continuous_rotGL_val : Continuous fun θ : ℝ => (rotGL θ).val := by
  refine continuous_matrix ?_
  simp only [Fin.forall_fin_two, rotGL_00, rotGL_01, rotGL_10, rotGL_11]
  exact ⟨⟨Real.continuous_cos, Real.continuous_sin.neg⟩, Real.continuous_sin,
    Real.continuous_cos⟩

theorem continuous_rotGL : Continuous rotGL := by
  refine Units.continuous_iff.2 ⟨continuous_rotGL_val, ?_⟩
  refine (continuous_rotGL_val.comp continuous_neg).congr fun x => ?_
  show (rotGL (-x)).val = ((rotGL x)⁻¹).val
  rw [rotGL_neg]

end TernaryPeriodPolynomials.Regularity

end
