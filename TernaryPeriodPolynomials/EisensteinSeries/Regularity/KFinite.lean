module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.KFiniteCore

@[expose] public section


/-!
# The lowest weight vectors are smooth vectors

For a finite-adelic model `M` and an element `e` fixed by an open compact subgroup, the lowest
weight vectors `lowestMinus hk e` and `lowestPlus hk e` of the holomorphic model are smooth
vectors: the finite part is immediate, and the archimedean orbit map `A ↦ g_A • lowestMinus e`
is real analytic on the invertible matrices.

For `det g > 0` the translate `g • lowestMinus e` is supported on the lower half plane, where it
equals `s • ((u w - v)^k)⁻¹ • e` with `u = g₁₁ + i g₁₀`, `v = g₀₁ + i g₀₀`; by
`kernel_eq_upperSeries` its scaled coefficients are `kernelScalar • qⁿ • vₙ`, so it corresponds to
`kernelScalar • theta Sum.inr (thetaVec k e) q` in `ℓ²(ℕ ⊕ ℕ; E)`, a real analytic function of `g`.
The case `det g < 0` is the same with the upper half plane, and `lowestPlus` is obtained from
`lowestMinus` by the reflection `diag(-1, 1)`.
-/

noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Elementwise
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors

namespace TernaryPeriodPolynomials.Regularity

/-! ### Entries of the inverse -/

theorem mul_inv_entry (g : GL (Fin 2) ℝ) (i j : Fin 2) :
    (1 : GL (Fin 2) ℝ).val i j = g.val i 0 * (g⁻¹).val 0 j + g.val i 1 * (g⁻¹).val 1 j := by
  rw [← gl_mul_apply, mul_inv_cancel]

theorem inv_val_00 (g : GL (Fin 2) ℝ) : (g⁻¹).val 0 0 = g.val 1 1 / g.val.det := by
  have E00 := mul_inv_entry g 0 0
  have E10 := mul_inv_entry g 1 0
  rw [gl_one_00] at E00
  rw [gl_one_10] at E10
  rw [eq_div_iff (gl_det_ne_zero g), gl_det_eq]
  linear_combination (-(g.val 1 1)) * E00 + (g.val 0 1) * E10

theorem inv_val_01 (g : GL (Fin 2) ℝ) : (g⁻¹).val 0 1 = -g.val 0 1 / g.val.det := by
  have E01 := mul_inv_entry g 0 1
  have E11 := mul_inv_entry g 1 1
  rw [gl_one_01] at E01
  rw [gl_one_11] at E11
  rw [eq_div_iff (gl_det_ne_zero g), gl_det_eq]
  linear_combination (-(g.val 1 1)) * E01 + (g.val 0 1) * E11

theorem inv_val_10 (g : GL (Fin 2) ℝ) : (g⁻¹).val 1 0 = -g.val 1 0 / g.val.det := by
  have E00 := mul_inv_entry g 0 0
  have E10 := mul_inv_entry g 1 0
  rw [gl_one_00] at E00
  rw [gl_one_10] at E10
  rw [eq_div_iff (gl_det_ne_zero g), gl_det_eq]
  linear_combination (g.val 1 0) * E00 - (g.val 0 0) * E10

theorem inv_val_11 (g : GL (Fin 2) ℝ) : (g⁻¹).val 1 1 = g.val 0 0 / g.val.det := by
  have E01 := mul_inv_entry g 0 1
  have E11 := mul_inv_entry g 1 1
  rw [gl_one_01] at E01
  rw [gl_one_11] at E11
  rw [eq_div_iff (gl_det_ne_zero g), gl_det_eq]
  linear_combination (-(g.val 0 0)) * E11 + (g.val 1 0) * E01

/-! ### The parameters `u`, `v`, `s` of a real matrix -/

/-- `u = A₁₁ + i A₁₀`. -/
def uOf (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (A 1 1 : ℂ) + Complex.I * (A 1 0 : ℂ)

/-- `v = A₀₁ + i A₀₀`. -/
def vOf (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (A 0 1 : ℂ) + Complex.I * (A 0 0 : ℂ)

/-- The real factor `|det A|^(-k/2) (det A)^k` as a complex number. -/
def sOf (k : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (((|A.det| ^ ((k : ℝ) / 2))⁻¹ * A.det ^ k : ℝ) : ℂ)

theorem norm_lt_of_det_pos {A : Matrix (Fin 2) (Fin 2) ℝ} (h : 0 < A.det) :
    ‖vOf A - Complex.I * uOf A‖ < ‖vOf A + Complex.I * uOf A‖ := by
  have h' := Matrix.det_fin_two A
  have h2 : ‖vOf A - Complex.I * uOf A‖ ^ 2 < ‖vOf A + Complex.I * uOf A‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [vOf, uOf, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    nlinarith
  by_contra hcon
  have h1 := mul_self_le_mul_self (norm_nonneg _) (not_lt.1 hcon)
  nlinarith

theorem norm_lt_of_det_neg {A : Matrix (Fin 2) (Fin 2) ℝ} (h : A.det < 0) :
    ‖vOf A + Complex.I * uOf A‖ < ‖vOf A - Complex.I * uOf A‖ := by
  have h' := Matrix.det_fin_two A
  have h2 : ‖vOf A + Complex.I * uOf A‖ ^ 2 < ‖vOf A - Complex.I * uOf A‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [vOf, uOf, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    nlinarith
  by_contra hcon
  have h1 := mul_self_le_mul_self (norm_nonneg _) (not_lt.1 hcon)
  nlinarith

theorem norm_lt_neg_of_det_pos {A : Matrix (Fin 2) (Fin 2) ℝ} (h : 0 < A.det) :
    ‖-vOf A - Complex.I * -uOf A‖ < ‖-vOf A + Complex.I * -uOf A‖ := by
  have e1 : -vOf A - Complex.I * -uOf A = -(vOf A - Complex.I * uOf A) := by ring
  have e2 : -vOf A + Complex.I * -uOf A = -(vOf A + Complex.I * uOf A) := by ring
  rw [e1, e2, norm_neg, norm_neg]
  exact norm_lt_of_det_pos h

theorem norm_lt_negv_of_det_neg {A : Matrix (Fin 2) (Fin 2) ℝ} (h : A.det < 0) :
    ‖-vOf A - Complex.I * uOf A‖ < ‖-vOf A + Complex.I * uOf A‖ := by
  have e1 : -vOf A - Complex.I * uOf A = -(vOf A + Complex.I * uOf A) := by ring
  have e2 : -vOf A + Complex.I * uOf A = -(vOf A - Complex.I * uOf A) := by ring
  rw [e1, e2, norm_neg, norm_neg]
  exact norm_lt_of_det_neg h

/-! ### The translate of the lowest weight vector -/

section Formula

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem im_moeb_inv_eq (g : GL (Fin 2) ℝ) {w : ℂ} :
    (moeb g⁻¹ w).im = (g.val.det)⁻¹ * w.im / Complex.normSq (denom g⁻¹ w) := by
  rw [im_moeb, gl_det_inv]

theorem im_moeb_inv_neg_of_pos {g : GL (Fin 2) ℝ} (hΔ : 0 < g.val.det) {w : ℂ}
    (hw : w.im < 0) : (moeb g⁻¹ w).im < 0 := by
  rw [im_moeb_inv_eq]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (inv_pos.2 hΔ) hw)
    (Complex.normSq_pos.2 (denom_ne_zero _ hw.ne))

theorem im_moeb_inv_pos_of_pos {g : GL (Fin 2) ℝ} (hΔ : 0 < g.val.det) {w : ℂ}
    (hw : 0 < w.im) : 0 < (moeb g⁻¹ w).im := by
  rw [im_moeb_inv_eq]
  exact div_pos (mul_pos (inv_pos.2 hΔ) hw) (Complex.normSq_pos.2 (denom_ne_zero _ hw.ne'))

theorem im_moeb_inv_neg_of_neg {g : GL (Fin 2) ℝ} (hΔ : g.val.det < 0) {w : ℂ}
    (hw : 0 < w.im) : (moeb g⁻¹ w).im < 0 := by
  rw [im_moeb_inv_eq]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (inv_lt_zero.2 hΔ) hw)
    (Complex.normSq_pos.2 (denom_ne_zero _ hw.ne'))

theorem im_moeb_inv_pos_of_neg {g : GL (Fin 2) ℝ} (hΔ : g.val.det < 0) {w : ℂ}
    (hw : w.im < 0) : 0 < (moeb g⁻¹ w).im := by
  rw [im_moeb_inv_eq]
  exact div_pos (mul_pos_of_neg_of_neg (inv_lt_zero.2 hΔ) hw)
    (Complex.normSq_pos.2 (denom_ne_zero _ hw.ne))

/-- Where the translate of `lowestMinus e` is nonzero it equals `s • ((u w - v)^k)⁻¹ • e`. -/
theorem realRep_lowestMinus_of_neg_im (hk : 2 ≤ k) (g : GL (Fin 2) ℝ) (e : E) {w : ℂ}
    (hw : w.im ≠ 0) (hm : (moeb g⁻¹ w).im < 0) :
    realRep k E g (lowestMinus hk e) w =
      sOf k g.val • ((uOf g.val * w - vOf g.val) ^ k)⁻¹ • e := by
  rw [realRep_apply g _ hw, lowestMinus_apply, ite_eq_left hm, smul_smul, smul_smul]
  congr 1
  have hdd : denom g⁻¹ w ≠ 0 := denom_ne_zero _ hw
  have hΔ : (g.val.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (gl_det_ne_zero g)
  have hmd : moeb g⁻¹ w * denom g⁻¹ w = ((g⁻¹).val 0 0 : ℂ) * w + ((g⁻¹).val 0 1 : ℂ) :=
    moeb_mul_denom hdd
  have key : denom g⁻¹ w * (moeb g⁻¹ w - Complex.I) =
      (uOf g.val * w - vOf g.val) / (g.val.det : ℂ) := by
    have e1 : denom g⁻¹ w * (moeb g⁻¹ w - Complex.I) =
        ((g⁻¹).val 0 0 : ℂ) * w + ((g⁻¹).val 0 1 : ℂ) - Complex.I * denom g⁻¹ w := by
      linear_combination hmd
    rw [e1, denom_def, inv_val_00, inv_val_01, inv_val_10, inv_val_11, uOf, vOf]
    push_cast
    field_simp
    ring
  have hk2 : (denom g⁻¹ w ^ k)⁻¹ * ((moeb g⁻¹ w - Complex.I) ^ k)⁻¹ =
      (g.val.det : ℂ) ^ k * ((uOf g.val * w - vOf g.val) ^ k)⁻¹ := by
    rw [← mul_inv, ← mul_pow, key, div_pow, inv_div, div_eq_mul_inv]
  have hfin : ∀ c : ℂ, c * (denom g⁻¹ w ^ k)⁻¹ * ((moeb g⁻¹ w - Complex.I) ^ k)⁻¹ =
      c * (g.val.det : ℂ) ^ k * ((uOf g.val * w - vOf g.val) ^ k)⁻¹ := fun c => by
    linear_combination c * hk2
  simp only [autFactor, sOf, Complex.ofReal_mul, Complex.ofReal_pow]
  exact hfin _

/-- Where `g⁻¹ w` lies in the upper half plane the translate of `lowestMinus e` vanishes. -/
theorem realRep_lowestMinus_of_pos_im (hk : 2 ≤ k) (g : GL (Fin 2) ℝ) (e : E) {w : ℂ}
    (hw : w.im ≠ 0) (hm : 0 < (moeb g⁻¹ w).im) : realRep k E g (lowestMinus hk e) w = 0 := by
  rw [realRep_apply g _ hw, lowestMinus_apply, ite_eq_right (not_lt.2 hm.le), smul_zero]

/-! ### Coefficients of the translate -/

theorem coeffMinus_realRep_of_pos (hk : 2 ≤ k) (g : GL (Fin 2) ℝ) (hΔ : 0 < g.val.det) (e : E)
    (n : ℕ) :
    coeffMinus (realRep k E g (lowestMinus hk e)) n =
      kernelCoeff k (sOf k g.val) (-uOf g.val) (-vOf g.val) e n := by
  unfold coeffMinus
  refine upperCoeff_of_eqOn_kernel (by omega) _ _ _ e (norm_lt_neg_of_det_pos hΔ)
    (fun z hz => ?_) n
  have hz' : 0 < z.im := hz
  have hnz : (-z).im ≠ 0 := by
    rw [Complex.neg_im]
    exact neg_ne_zero.2 hz'.ne'
  have him : (moeb g⁻¹ (-z)).im < 0 :=
    im_moeb_inv_neg_of_pos hΔ (by rw [Complex.neg_im]; linarith)
  show realRep k E g (lowestMinus hk e) (-z) = _
  rw [realRep_lowestMinus_of_neg_im hk g e hnz him,
    show uOf g.val * (-z) - vOf g.val = (-uOf g.val) * z + (-vOf g.val) by ring]

theorem coeffPlus_realRep_of_pos (hk : 2 ≤ k) (g : GL (Fin 2) ℝ) (hΔ : 0 < g.val.det) (e : E)
    (n : ℕ) : coeffPlus (realRep k E g (lowestMinus hk e)) n = 0 := by
  unfold coeffPlus
  refine upperCoeff_of_eqOn_zero (fun z hz => ?_) n
  have hz' : 0 < z.im := hz
  exact realRep_lowestMinus_of_pos_im hk g e hz'.ne' (im_moeb_inv_pos_of_pos hΔ hz')

theorem coeffPlus_realRep_of_neg (hk : 2 ≤ k) (g : GL (Fin 2) ℝ) (hΔ : g.val.det < 0) (e : E)
    (n : ℕ) :
    coeffPlus (realRep k E g (lowestMinus hk e)) n =
      kernelCoeff k (sOf k g.val) (uOf g.val) (-vOf g.val) e n := by
  unfold coeffPlus
  refine upperCoeff_of_eqOn_kernel (by omega) _ _ _ e (norm_lt_negv_of_det_neg hΔ)
    (fun z hz => ?_) n
  have hz' : 0 < z.im := hz
  have him : (moeb g⁻¹ z).im < 0 := im_moeb_inv_neg_of_neg hΔ hz'
  rw [realRep_lowestMinus_of_neg_im hk g e hz'.ne' him,
    show uOf g.val * z - vOf g.val = uOf g.val * z + (-vOf g.val) by ring]

theorem coeffMinus_realRep_of_neg (hk : 2 ≤ k) (g : GL (Fin 2) ℝ) (hΔ : g.val.det < 0) (e : E)
    (n : ℕ) : coeffMinus (realRep k E g (lowestMinus hk e)) n = 0 := by
  unfold coeffMinus
  refine upperCoeff_of_eqOn_zero (fun z hz => ?_) n
  have hz' : 0 < z.im := hz
  have hnz : (-z).im ≠ 0 := by
    rw [Complex.neg_im]
    exact neg_ne_zero.2 hz'.ne'
  show realRep k E g (lowestMinus hk e) (-z) = 0
  exact realRep_lowestMinus_of_pos_im hk g e hnz
    (im_moeb_inv_pos_of_neg hΔ (by rw [Complex.neg_im]; linarith))

/-! ### The translate in `ℓ²(ℕ ⊕ ℕ; E)` -/

theorem bergmanToLp_realRep_of_pos (hk : 2 ≤ k) (g : GL (Fin 2) ℝ) (hΔ : 0 < g.val.det)
    (e : E) :
    bergmanToLp hk (realRep k E g (lowestMinus hk e)) =
      kernelScalar k (sOf k g.val) (-uOf g.val) (-vOf g.val) •
        theta Sum.inr (thetaVec k e) (kernelRatio (-uOf g.val) (-vOf g.val)) := by
  have hq := norm_kernelRatio_lt_one (norm_lt_neg_of_det_pos hΔ)
  refine lp.ext (funext fun j => ?_)
  rcases j with n | n
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffPlus (realRep k E g (lowestMinus hk e)) n = _
    rw [coeffPlus_realRep_of_pos hk g hΔ e n, smul_zero]
    show (0 : E) = kernelScalar k (sOf k g.val) (-uOf g.val) (-vOf g.val) •
      theta Sum.inr (thetaVec k e) (kernelRatio (-uOf g.val) (-vOf g.val)) (Sum.inl n)
    rw [theta_apply_of_forall_ne Sum.inr (norm_thetaVec_le hk e) hq (Sum.inl n)
      (fun m => Sum.inr_ne_inl), smul_zero]
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffMinus (realRep k E g (lowestMinus hk e)) n = _
    rw [coeffMinus_realRep_of_pos hk g hΔ e n]
    show _ = kernelScalar k (sOf k g.val) (-uOf g.val) (-vOf g.val) •
      theta Sum.inr (thetaVec k e) (kernelRatio (-uOf g.val) (-vOf g.val)) (Sum.inr n)
    rw [theta_apply_self Sum.inr Sum.inr_injective (norm_thetaVec_le hk e) hq n]
    unfold kernelCoeff thetaVec
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    unfold binomCoeff
    push_cast
    ring

theorem bergmanToLp_realRep_of_neg (hk : 2 ≤ k) (g : GL (Fin 2) ℝ) (hΔ : g.val.det < 0)
    (e : E) :
    bergmanToLp hk (realRep k E g (lowestMinus hk e)) =
      kernelScalar k (sOf k g.val) (uOf g.val) (-vOf g.val) •
        theta Sum.inl (thetaVec k e) (kernelRatio (uOf g.val) (-vOf g.val)) := by
  have hq := norm_kernelRatio_lt_one (norm_lt_negv_of_det_neg hΔ)
  refine lp.ext (funext fun j => ?_)
  rcases j with n | n
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffPlus (realRep k E g (lowestMinus hk e)) n = _
    rw [coeffPlus_realRep_of_neg hk g hΔ e n]
    show _ = kernelScalar k (sOf k g.val) (uOf g.val) (-vOf g.val) •
      theta Sum.inl (thetaVec k e) (kernelRatio (uOf g.val) (-vOf g.val)) (Sum.inl n)
    rw [theta_apply_self Sum.inl Sum.inl_injective (norm_thetaVec_le hk e) hq n]
    unfold kernelCoeff thetaVec
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    unfold binomCoeff
    push_cast
    ring
  · show ((bergmanScale k n : ℝ) : ℂ) • coeffMinus (realRep k E g (lowestMinus hk e)) n = _
    rw [coeffMinus_realRep_of_neg hk g hΔ e n, smul_zero]
    show (0 : E) = kernelScalar k (sOf k g.val) (uOf g.val) (-vOf g.val) •
      theta Sum.inl (thetaVec k e) (kernelRatio (uOf g.val) (-vOf g.val)) (Sum.inr n)
    rw [theta_apply_of_forall_ne Sum.inl (norm_thetaVec_le hk e) hq (Sum.inr n)
      (fun m => Sum.inl_ne_inr), smul_zero]

end Formula

/-! ### Smoothness in the matrix -/

section Smooth

theorem contDiff_entry (i j : Fin 2) :
    ContDiff ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) := by
  have h : ContDiff ℝ ⊤ (fun A : Fin 2 → Fin 2 → ℝ => A i j) :=
    (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)
  exact h

theorem contDiff_entry_complex (i j : Fin 2) :
    ContDiff ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ => ((A i j : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_entry i j)

theorem contDiff_uOf : ContDiff ℝ ⊤ uOf :=
  (contDiff_entry_complex 1 1).add (contDiff_const.mul (contDiff_entry_complex 1 0))

theorem contDiff_vOf : ContDiff ℝ ⊤ vOf :=
  (contDiff_entry_complex 0 1).add (contDiff_const.mul (contDiff_entry_complex 0 0))

theorem contDiff_det : ContDiff ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det) := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det) =
      fun A => A 0 0 * A 1 1 - A 0 1 * A 1 0 := funext Matrix.det_fin_two
  rw [h]
  exact ((contDiff_entry 0 0).mul (contDiff_entry 1 1)).sub
    ((contDiff_entry 0 1).mul (contDiff_entry 1 0))

/-- Smoothness of `sOf` on a set where `|det A|` is a smooth positive function `d`. -/
theorem contDiffOn_sOf (k : ℕ) {s : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    {d : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hd : ContDiff ℝ ⊤ d) (hpos : ∀ A ∈ s, 0 < d A)
    (habs : ∀ A ∈ s, |A.det| = d A) : ContDiffOn ℝ ⊤ (sOf k) s := by
  have hr : ContDiffOn ℝ ⊤ (fun A => d A ^ ((k : ℝ) / 2)) s := fun A hA =>
    ((Real.contDiffAt_rpow_const_of_ne (n := ⊤) (p := (k : ℝ) / 2) (hpos A hA).ne').comp A
      hd.contDiffAt).contDiffWithinAt
  have hinv : ContDiffOn ℝ ⊤ (fun A => (d A ^ ((k : ℝ) / 2))⁻¹) s :=
    hr.inv fun A hA => (Real.rpow_pos_of_pos (hpos A hA) _).ne'
  have hreal : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (d A ^ ((k : ℝ) / 2))⁻¹ * A.det ^ k) s :=
    hinv.mul (contDiff_det.pow k).contDiffOn
  have hc : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (((d A ^ ((k : ℝ) / 2))⁻¹ * A.det ^ k : ℝ) : ℂ)) s :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hreal
  refine hc.congr fun A hA => ?_
  simp only [sOf, habs A hA]

theorem contDiffOn_kernelRatio {s : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    {u v : Matrix (Fin 2) (Fin 2) ℝ → ℂ} (hu : ContDiffOn ℝ ⊤ u s) (hv : ContDiffOn ℝ ⊤ v s)
    (h0 : ∀ A ∈ s, v A + Complex.I * u A ≠ 0) :
    ContDiffOn ℝ ⊤ (fun A => kernelRatio (u A) (v A)) s := by
  have h1 : ContDiffOn ℝ ⊤ (fun A => v A - Complex.I * u A) s :=
    hv.sub (contDiffOn_const.mul hu)
  have h2 : ContDiffOn ℝ ⊤ (fun A => (v A + Complex.I * u A)⁻¹) s :=
    (hv.add (contDiffOn_const.mul hu)).inv h0
  exact (h1.mul h2).congr fun A _ => by simp only [kernelRatio, div_eq_mul_inv]

theorem contDiffOn_kernelScalar (k : ℕ) {s : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    {r u v : Matrix (Fin 2) (Fin 2) ℝ → ℂ} (hr : ContDiffOn ℝ ⊤ r s)
    (hu : ContDiffOn ℝ ⊤ u s) (hv : ContDiffOn ℝ ⊤ v s)
    (h0 : ∀ A ∈ s, v A + Complex.I * u A ≠ 0) :
    ContDiffOn ℝ ⊤ (fun A => kernelScalar k (r A) (u A) (v A)) s := by
  have h2 : ContDiffOn ℝ ⊤ (fun A => ((v A + Complex.I * u A) ^ k)⁻¹) s :=
    ((hv.add (contDiffOn_const.mul hu)).pow k).inv fun A hA => pow_ne_zero k (h0 A hA)
  exact (hr.mul contDiffOn_const).mul h2

end Smooth

/-! ### Analyticity of the orbit map of `lowestMinus` -/

section Orbit

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem invertibleMatrix_val_of_det {A : Matrix (Fin 2) (Fin 2) ℝ} (h : A.det ≠ 0) :
    (invertibleMatrix A).val = A := by
  unfold invertibleMatrix
  rw [dite_eq_left h]
  exact Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- The inverse of `bergmanToLp` as a continuous real linear map. -/
def lpToBergman (hk : 2 ≤ k) : lp (fun _ : ℕ ⊕ ℕ => E) 2 →L[ℝ] BergmanSpace k E :=
  ((bergmanEquivLp hk).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ

theorem lpToBergman_apply (hk : 2 ≤ k) (f : lp (fun _ : ℕ ⊕ ℕ => E) 2) :
    lpToBergman hk f = (bergmanEquivLp hk).symm f := rfl

theorem lpToBergman_toLp (hk : 2 ≤ k) (F : BergmanSpace k E) :
    lpToBergman hk (bergmanToLp hk F) = F :=
  (bergmanEquivLp hk).symm_apply_apply F

theorem contDiffOn_orbit_pos (hk : 2 ≤ k) (e : E) :
    ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      realRep k E (invertibleMatrix A) (lowestMinus hk e)) {A | 0 < A.det} := by
  have hu : ContDiffOn ℝ ⊤ (fun A => -uOf A) {A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A.det} :=
    contDiff_uOf.neg.contDiffOn
  have hv : ContDiffOn ℝ ⊤ (fun A => -vOf A) {A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A.det} :=
    contDiff_vOf.neg.contDiffOn
  have h0 : ∀ A ∈ {A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A.det},
      -vOf A + Complex.I * -uOf A ≠ 0 := fun A hA =>
    kernel_denom_ne_zero (norm_lt_neg_of_det_pos hA)
  have hs : ContDiffOn ℝ ⊤ (sOf k) {A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A.det} :=
    contDiffOn_sOf k (d := fun A => A.det) contDiff_det (fun A hA => hA)
      (fun A hA => abs_of_pos hA)
  have hq := contDiffOn_kernelRatio hu hv h0
  have hscal := contDiffOn_kernelScalar k hs hu hv h0
  have hθ := (contDiffOn_theta Sum.inr (norm_thetaVec_le hk e)).comp hq
    (fun A hA => mem_ball_zero_iff.2 (norm_kernelRatio_lt_one (norm_lt_neg_of_det_pos hA)))
  have hF := hscal.smul hθ
  refine ((lpToBergman hk).contDiff.comp_contDiffOn hF).congr fun A hA => ?_
  have hApos : 0 < A.det := hA
  have hg : (invertibleMatrix A).val = A := invertibleMatrix_val_of_det hApos.ne'
  have h1 := bergmanToLp_realRep_of_pos hk (invertibleMatrix A) (by rw [hg]; exact hApos) e
  rw [hg] at h1
  show realRep k E (invertibleMatrix A) (lowestMinus hk e) = lpToBergman hk
    (kernelScalar k (sOf k A) (-uOf A) (-vOf A) •
      theta Sum.inr (thetaVec k e) (kernelRatio (-uOf A) (-vOf A)))
  rw [← h1, lpToBergman_toLp]

theorem contDiffOn_orbit_neg (hk : 2 ≤ k) (e : E) :
    ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      realRep k E (invertibleMatrix A) (lowestMinus hk e)) {A | A.det < 0} := by
  have hu : ContDiffOn ℝ ⊤ (fun A => uOf A) {A : Matrix (Fin 2) (Fin 2) ℝ | A.det < 0} :=
    contDiff_uOf.contDiffOn
  have hv : ContDiffOn ℝ ⊤ (fun A => -vOf A) {A : Matrix (Fin 2) (Fin 2) ℝ | A.det < 0} :=
    contDiff_vOf.neg.contDiffOn
  have h0 : ∀ A ∈ {A : Matrix (Fin 2) (Fin 2) ℝ | A.det < 0},
      -vOf A + Complex.I * uOf A ≠ 0 := fun A hA =>
    kernel_denom_ne_zero (norm_lt_negv_of_det_neg hA)
  have hs : ContDiffOn ℝ ⊤ (sOf k) {A : Matrix (Fin 2) (Fin 2) ℝ | A.det < 0} :=
    contDiffOn_sOf k (d := fun A => -A.det) contDiff_det.neg (fun A hA => neg_pos.2 hA)
      (fun A hA => abs_of_neg hA)
  have hq := contDiffOn_kernelRatio hu hv h0
  have hscal := contDiffOn_kernelScalar k hs hu hv h0
  have hθ := (contDiffOn_theta Sum.inl (norm_thetaVec_le hk e)).comp hq
    (fun A hA => mem_ball_zero_iff.2 (norm_kernelRatio_lt_one (norm_lt_negv_of_det_neg hA)))
  have hF := hscal.smul hθ
  refine ((lpToBergman hk).contDiff.comp_contDiffOn hF).congr fun A hA => ?_
  have hAneg : A.det < 0 := hA
  have hg : (invertibleMatrix A).val = A := invertibleMatrix_val_of_det hAneg.ne
  have h1 := bergmanToLp_realRep_of_neg hk (invertibleMatrix A) (by rw [hg]; exact hAneg) e
  rw [hg] at h1
  show realRep k E (invertibleMatrix A) (lowestMinus hk e) = lpToBergman hk
    (kernelScalar k (sOf k A) (uOf A) (-vOf A) •
      theta Sum.inl (thetaVec k e) (kernelRatio (uOf A) (-vOf A)))
  rw [← h1, lpToBergman_toLp]

/-- **Analyticity of the orbit map** of `lowestMinus e` on the invertible matrices. -/
theorem contDiffOn_orbit_lowestMinus (hk : 2 ≤ k) (e : E) :
    ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      realRep k E (invertibleMatrix A) (lowestMinus hk e)) {A | A.det ≠ 0} := by
  have hopen₁ : IsOpen {A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A.det} :=
    isOpen_lt continuous_const continuous_id.matrix_det
  have hopen₂ : IsOpen {A : Matrix (Fin 2) (Fin 2) ℝ | A.det < 0} :=
    isOpen_lt continuous_id.matrix_det continuous_const
  refine ((contDiffOn_orbit_pos hk e).union_of_isOpen (contDiffOn_orbit_neg hk e) hopen₁
    hopen₂).mono ?_
  intro A hA
  rcases lt_or_gt_of_ne hA with h | h
  · exact Or.inr h
  · exact Or.inl h

end Orbit

/-! ### The reflection `diag(-1, 1)` and `lowestPlus` -/

section Reflection

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The matrix `diag(-1, 1)`. -/
def reflMat : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]

theorem det_reflMat : reflMat.det = -1 := by
  rw [reflMat, Matrix.det_fin_two_of]
  norm_num

/-- The reflection `diag(-1, 1)` as an element of `GL₂(ℝ)`. -/
def reflGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero reflMat (by rw [det_reflMat]; norm_num)

theorem reflGL_val : reflGL.val = reflMat :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem reflGL_mul_self : reflGL * reflGL = 1 := by
  apply Units.ext
  rw [Units.val_mul, reflGL_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem reflGL_inv : reflGL⁻¹ = reflGL := inv_eq_of_mul_eq_one_right reflGL_mul_self

theorem denom_reflGL (w : ℂ) : denom reflGL w = 1 := by
  rw [denom_def, reflGL_val]
  simp [reflMat]

theorem moeb_reflGL (w : ℂ) : moeb reflGL w = -w := by
  rw [moeb_def, denom_reflGL, reflGL_val]
  simp [reflMat]

omit [CompleteSpace E] in
theorem realRep_refl_apply (F : BergmanSpace k E) {w : ℂ} (hw : w.im ≠ 0) :
    realRep k E reflGL F w = F (-w) := by
  have hfac : autFactor k reflGL w = 1 := by
    unfold autFactor
    rw [reflGL_inv, denom_reflGL, reflGL_val, det_reflMat]
    simp
  rw [realRep_apply _ F hw, hfac, reflGL_inv, moeb_reflGL, one_smul]

theorem lowestPlus_eq_realRep_refl (hk : 2 ≤ k) (e : E) :
    lowestPlus hk e = ((-1 : ℂ) ^ k) • realRep k E reflGL (lowestMinus hk e) := by
  refine BergmanSpace.ext fun w => ?_
  by_cases hw : w.im = 0
  · rw [BergmanSpace.smul_apply, realRep_apply_of_im_eq_zero _ _ hw, smul_zero,
      lowestPlus_apply, ite_eq_right (by rw [hw]; exact lt_irrefl _)]
  · rw [BergmanSpace.smul_apply, realRep_refl_apply _ hw, lowestMinus_apply, lowestPlus_apply]
    rcases lt_or_gt_of_ne hw with hneg | hpos
    · have h1 : ¬ (0 < w.im) := not_lt.2 hneg.le
      have h2 : ¬ ((-w).im < 0) := by
        rw [Complex.neg_im]
        linarith
      rw [ite_eq_right h1, ite_eq_right h2, smul_zero]
    · have h2 : (-w).im < 0 := by
        rw [Complex.neg_im]
        linarith
      rw [ite_eq_left hpos, ite_eq_left h2, smul_smul]
      congr 1
      have h3 : (-w - Complex.I) = -(w + Complex.I) := by ring
      have hne : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [h3, neg_pow (w + Complex.I) k, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem invertibleMatrix_mul_refl {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    invertibleMatrix (A * reflMat) = invertibleMatrix A * reflGL := by
  have hAr : (A * reflMat).det ≠ 0 := by
    rw [Matrix.det_mul, det_reflMat]
    simpa using hA
  apply Units.ext
  rw [Units.val_mul]
  unfold invertibleMatrix
  rw [dite_eq_left hAr, dite_eq_left hA, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, reflGL_val]

/-- Right multiplication by a matrix, as a continuous linear map. -/
def mulRightCLM (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ A)

theorem mulRightCLM_apply (A B : Matrix (Fin 2) (Fin 2) ℝ) : mulRightCLM A B = B * A := rfl

/-- **Analyticity of the orbit map** of `lowestPlus e` on the invertible matrices. -/
theorem contDiffOn_orbit_lowestPlus (hk : 2 ≤ k) (e : E) :
    ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      realRep k E (invertibleMatrix A) (lowestPlus hk e)) {A | A.det ≠ 0} := by
  have hR : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ => A * reflMat)
      {A | A.det ≠ 0} := (mulRightCLM reflMat).contDiff.contDiffOn
  have h2 : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      realRep k E (invertibleMatrix (A * reflMat)) (lowestMinus hk e)) {A | A.det ≠ 0} :=
    (contDiffOn_orbit_lowestMinus hk e).comp hR fun A hA => by
      show (A * reflMat).det ≠ 0
      rw [Matrix.det_mul, det_reflMat]
      simpa using (show A.det ≠ 0 from hA)
  refine (h2.const_smul ((-1 : ℂ) ^ k)).congr fun A hA => ?_
  have hA' : A.det ≠ 0 := hA
  show realRep k E (invertibleMatrix A) (lowestPlus hk e) =
    ((-1 : ℂ) ^ k) • realRep k E (invertibleMatrix (A * reflMat)) (lowestMinus hk e)
  rw [lowestPlus_eq_realRep_refl hk e, map_smul, invertibleMatrix_mul_refl hA', map_mul,
    Module.End.mul_apply]

end Reflection

/-! ### Smooth vectors -/

section Main

variable {k : ℕ}

/-- The archimedean orbit map of a vector with smooth orbit map on the invertible matrices. -/
theorem smooth_of_contDiffOn_orbit (M : FiniteModel k) (v : BergmanSpace k M.E)
    (h : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      realRep k M.E (invertibleMatrix A) v) {A | A.det ≠ 0}) :
    Smooth (fun x : Fin 1 → BinaryRealGL => bergmanRep M (atInfinity (x 0)) v) := by
  unfold Smooth
  have hmaps : Set.MapsTo (fun A : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ => A 0)
      {A | ∀ i, (A i).det ≠ 0} {A : Matrix (Fin 2) (Fin 2) ℝ | A.det ≠ 0} := fun A hA => hA 0
  have h' := h.comp (contDiff_apply (𝕜 := ℝ) (E := Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 1)).contDiffOn
    hmaps
  refine h'.congr fun A hA => ?_
  simp only [Function.comp, bergmanRep_atInfinity]

/-- **The lower lowest weight vector is a smooth vector.** -/
theorem isSmoothVector_lowestMinus (M : FiniteModel k) (hk : 2 ≤ k)
    {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) {e : M.E}
    (he : e ∈ fixedSubmodule M.σ U) : IsSmoothVector (bergmanRep M) (lowestMinus hk e) := by
  refine ⟨smooth_of_contDiffOn_orbit M _ (contDiffOn_orbit_lowestMinus hk e),
    U, hU.1, hU.2, fun u => ?_⟩
  rw [bergmanRep_atFinite]
  refine BergmanSpace.ext fun w => ?_
  rw [finRep_apply, lowestMinus_apply]
  split_ifs
  · rw [map_smul, he u]
  · exact map_zero _

/-- **The upper lowest weight vector is a smooth vector.** -/
theorem isSmoothVector_lowestPlus (M : FiniteModel k) (hk : 2 ≤ k)
    {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) {e : M.E}
    (he : e ∈ fixedSubmodule M.σ U) : IsSmoothVector (bergmanRep M) (lowestPlus hk e) := by
  refine ⟨smooth_of_contDiffOn_orbit M _ (contDiffOn_orbit_lowestPlus hk e),
    U, hU.1, hU.2, fun u => ?_⟩
  rw [bergmanRep_atFinite]
  refine BergmanSpace.ext fun w => ?_
  rw [finRep_apply, lowestPlus_apply]
  split_ifs
  · rw [map_smul, he u]
  · exact map_zero _

end Main

end TernaryPeriodPolynomials.Regularity

end
