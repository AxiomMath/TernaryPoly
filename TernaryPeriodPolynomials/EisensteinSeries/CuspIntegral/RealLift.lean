module

public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Basic
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.ModularForms.QExpansion

@[expose] public section


/-!
# The real lift of a `Γ₁(3)` cusp form

Modularity, boundedness, the central sign and the vanishing of the zeroth Fourier coefficient
along every unipotent line for `liftReal`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix ModularForm
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open scoped Pointwise

noncomputable section

namespace TernaryPeriodPolynomials.CuspIntegral

theorem sigma_apply_of_pos {r : BinaryRealGL} (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val)
    (z : ℂ) : UpperHalfPlane.σ r z = z := by
  have hr' : 0 < (r : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← GeneralLinearGroup.val_det_apply]
  simp [UpperHalfPlane.σ, hr']

theorem det_mapGL (σ : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ σ) = 1 :=
  SpecialLinearGroup.det_mapGL σ

theorem det_unipotent (y : ℝ) : GeneralLinearGroup.det (binaryUnipotent y) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, binaryUnipotent, Matrix.det_fin_two]

theorem det_mapGL_unipotent_mul (σ : SpecialLinearGroup (Fin 2) ℤ) (y : ℝ) (r : BinaryRealGL) :
    GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ σ * binaryUnipotent y * r) =
      GeneralLinearGroup.det r := by
  rw [map_mul, map_mul, det_mapGL, det_unipotent, one_mul, one_mul]

/-- The weight-`k` lift of an arbitrary function on `ℍ`. -/
def liftRealG (k : ℤ) (g : UpperHalfPlane → ℂ) (r : BinaryRealGL) : ℂ :=
  ((Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| : ℝ) : ℂ) ^ k *
    UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ) ^ (-k) * g (r • UpperHalfPlane.I)

theorem liftReal_eq {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (r : BinaryRealGL) :
    liftReal f r = liftRealG k f r := rfl

theorem liftRealG_mapGL_mul (k : ℤ) (g : UpperHalfPlane → ℂ)
    (σ : SpecialLinearGroup (Fin 2) ℤ) (s : BinaryRealGL)
    (hs : 0 < (GeneralLinearGroup.det s : ℝˣ).val) :
    liftRealG k g (SpecialLinearGroup.mapGL ℝ σ * s) =
      liftRealG k (g ∣[k] SpecialLinearGroup.mapGL ℝ σ) s := by
  have hdet : GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ σ * s) =
      GeneralLinearGroup.det s := by
    rw [map_mul, det_mapGL, one_mul]
  have hσ : 0 < (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ σ) : ℝˣ).val := by
    rw [det_mapGL]
    exact one_pos
  unfold liftRealG
  rw [hdet, mul_smul, ModularForm.slash_apply, UpperHalfPlane.denom_cocycle_σ,
    sigma_apply_of_pos hs, sigma_apply_of_pos hσ, mul_zpow]
  simp only [det_mapGL, Units.val_one, abs_one, Complex.ofReal_one, _root_.one_zpow]
  ring

theorem liftReal_gamma1 {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (δ : SpecialLinearGroup (Fin 2) ℤ) (hδ : δ ∈ CongruenceSubgroup.Gamma1 3)
    (r : BinaryRealGL) (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    liftReal f (SpecialLinearGroup.mapGL ℝ δ * r) = liftReal f r := by
  have hmem : SpecialLinearGroup.mapGL ℝ δ ∈ binaryRealGammaOneThree := ⟨δ, hδ, rfl⟩
  rw [liftReal_eq, liftReal_eq, liftRealG_mapGL_mul k _ δ r hr,
    SlashInvariantFormClass.slash_action_eq f _ hmem]

/-! ### Boundedness -/

theorem norm_liftReal {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (r : BinaryRealGL)
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    ‖liftReal f r‖ = (Real.sqrt (GeneralLinearGroup.det r : ℝˣ).val /
      ‖UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ)‖) ^ k *
        ‖f (r • UpperHalfPlane.I)‖ := by
  rw [liftReal_eq]
  unfold liftRealG
  rw [norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_real, Real.norm_of_nonneg
    (Real.sqrt_nonneg _), abs_of_pos hr, div_zpow, _root_.zpow_neg, div_eq_mul_inv]

theorem im_smul_I (r : BinaryRealGL) (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    (r • UpperHalfPlane.I).im = (GeneralLinearGroup.det r : ℝˣ).val /
      ‖UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ)‖ ^ 2 := by
  rw [UpperHalfPlane.im_smul_eq_div_normSq, abs_of_pos hr, UpperHalfPlane.I_im, mul_one,
    Complex.normSq_eq_norm_sq]

theorem liftReal_bounded {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) :
    ∃ C : ℝ, ∀ r : BinaryRealGL, 0 < (GeneralLinearGroup.det r : ℝˣ).val →
      ‖liftReal f r‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun r hr => ?_⟩
  have hNpos : 0 < ‖UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ)‖ :=
    norm_pos_iff.mpr (UpperHalfPlane.denom_ne_zero r UpperHalfPlane.I)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (GeneralLinearGroup.det r : ℝˣ).val /
      ‖UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ)‖ := ⟨_, rfl⟩
  have hspos : 0 < s := by
    rw [hs]
    exact div_pos (Real.sqrt_pos.mpr hr) hNpos
  have him : (r • UpperHalfPlane.I).im = s ^ 2 := by
    rw [im_smul_I r hr, hs, div_pow, Real.sq_sqrt hr.le]
  have hpow : (r • UpperHalfPlane.I).im ^ ((k : ℝ) / 2) = s ^ k := by
    rw [him, ← Real.rpow_natCast, ← Real.rpow_mul hspos.le]
    have : ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) := by push_cast; ring
    rw [this, Real.rpow_intCast]
  rw [norm_liftReal f r hr, ← hs]
  have h1 := hC (r • UpperHalfPlane.I)
  rw [hpow] at h1
  have hk : 0 < s ^ k := zpow_pos hspos k
  calc s ^ k * ‖f (r • UpperHalfPlane.I)‖ ≤ s ^ k * (C / s ^ k) :=
        mul_le_mul_of_nonneg_left h1 hk.le
    _ = C := mul_div_cancel₀ _ hk.ne'

/-! ### Scalars -/

theorem det_scalar_real (t : ℝˣ) :
    (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) t) : ℝˣ).val = t.val ^ 2 := by
  rw [GeneralLinearGroup.det_scalar]
  simp

theorem liftReal_scalar {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (t : ℝˣ)
    (r : BinaryRealGL) (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    liftReal f (GeneralLinearGroup.scalar (Fin 2) t * r) =
      (if t.val < 0 then (-1 : ℂ) ^ k else 1) * liftReal f r := by
  have hdet : (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) t * r) : ℝˣ).val =
      t.val ^ 2 * (GeneralLinearGroup.det r : ℝˣ).val := by
    rw [map_mul, Units.val_mul, det_scalar_real]
  have hden : UpperHalfPlane.denom (GeneralLinearGroup.scalar (Fin 2) t * r)
      (UpperHalfPlane.I : ℂ) = (t.val : ℂ) * UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ) := by
    rw [UpperHalfPlane.denom_cocycle_σ, UpperHalfPlane.denom_scalar, sigma_apply_of_pos hr]
  have hsmul : (GeneralLinearGroup.scalar (Fin 2) t * r) • UpperHalfPlane.I =
      r • UpperHalfPlane.I := by
    rw [mul_smul, UpperHalfPlane.glScalar_smul]
  have ht0 : t.val ≠ 0 := t.ne_zero
  have hsq : Real.sqrt |t.val ^ 2 * (GeneralLinearGroup.det r : ℝˣ).val| =
      |t.val| * Real.sqrt (GeneralLinearGroup.det r : ℝˣ).val := by
    rw [abs_mul, abs_pow, sq_abs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_pos hr]
  rw [liftReal_eq, liftReal_eq]
  unfold liftRealG
  rw [hdet, hden, hsmul, hsq, abs_of_pos hr, mul_zpow, Complex.ofReal_mul, mul_zpow,
    _root_.zpow_neg, _root_.zpow_neg]
  have htc : (t.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
  have hk : ((t.val : ℂ) ^ k) ≠ 0 := zpow_ne_zero _ htc
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · rw [ite_eq_left hneg, abs_of_neg hneg, Complex.ofReal_neg]
    have hnz : (-(t.val : ℂ)) ^ k = (-1) ^ k * (t.val : ℂ) ^ k := by
      rw [neg_eq_neg_one_mul, mul_zpow]
    rw [hnz]
    field_simp
  · rw [ite_eq_right (not_lt.mpr hpos.le), abs_of_pos hpos]
    field_simp

/-! ### Unipotent lines -/

theorem unipotent_smul (y : ℝ) (z : UpperHalfPlane) : binaryUnipotent y • z = y +ᵥ z := by
  have hdet : 0 < (GeneralLinearGroup.det (binaryUnipotent y) : ℝˣ).val := by
    rw [det_unipotent]
    exact one_pos
  ext
  rw [UpperHalfPlane.coe_smul, sigma_apply_of_pos hdet, UpperHalfPlane.coe_vadd]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, binaryUnipotent, add_comm]

theorem liftRealG_unipotent_mul (k : ℤ) (g : UpperHalfPlane → ℂ) (y : ℝ) (r : BinaryRealGL)
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    liftRealG k g (binaryUnipotent y * r) =
      ((Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| : ℝ) : ℂ) ^ k *
        UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ) ^ (-k) * g (y +ᵥ (r • UpperHalfPlane.I)) := by
  have hdet : 0 < (GeneralLinearGroup.det (binaryUnipotent y) : ℝˣ).val := by
    rw [det_unipotent]
    exact one_pos
  have hden : UpperHalfPlane.denom (binaryUnipotent y * r) (UpperHalfPlane.I : ℂ) =
      UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ) := by
    rw [UpperHalfPlane.denom_cocycle_σ, sigma_apply_of_pos hr]
    simp [UpperHalfPlane.denom, binaryUnipotent]
  unfold liftRealG
  rw [map_mul, det_unipotent, one_mul, hden, mul_smul, unipotent_smul]

theorem liftReal_unipotent_eq {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (σ : SpecialLinearGroup (Fin 2) ℤ) (r : BinaryRealGL)
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) (y : ℝ) :
    liftReal f (SpecialLinearGroup.mapGL ℝ σ * binaryUnipotent y * r) =
      ((Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| : ℝ) : ℂ) ^ k *
        UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ) ^ (-k) *
          (⇑f ∣[k] SpecialLinearGroup.mapGL ℝ σ) (y +ᵥ (r • UpperHalfPlane.I)) := by
  have hn : 0 < (GeneralLinearGroup.det (binaryUnipotent y * r) : ℝˣ).val := by
    rw [map_mul, det_unipotent, one_mul]
    exact hr
  rw [mul_assoc, liftReal_eq, liftRealG_mapGL_mul k _ σ _ hn,
    liftRealG_unipotent_mul k _ y r hr]

/-- The integral matrix `[[1, 3], [0, 1]]`. -/
def T3 : SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, 3; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem T3_mem_gamma : T3 ∈ CongruenceSubgroup.Gamma 3 := by
  rw [CongruenceSubgroup.Gamma_mem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem gamma_le_gamma1 {δ : SpecialLinearGroup (Fin 2) ℤ}
    (h : δ ∈ CongruenceSubgroup.Gamma 3) : δ ∈ CongruenceSubgroup.Gamma1 3 := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨h.1, h.2.2.2, h.2.2.1⟩

theorem conj_T3_mem (σ : SpecialLinearGroup (Fin 2) ℤ) :
    σ * T3 * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 3 :=
  gamma_le_gamma1 ((CongruenceSubgroup.Gamma_normal (N := 3)).conj_mem T3 T3_mem_gamma σ)

theorem mapGL_T3 : SpecialLinearGroup.mapGL ℝ T3 = binaryUnipotent (3 : ℝ) := by
  apply Units.ext
  ext i j
  rw [SpecialLinearGroup.mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [T3, binaryUnipotent]

theorem liftReal_unipotent_periodic {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (σ : SpecialLinearGroup (Fin 2) ℤ) (r : BinaryRealGL)
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) (y : ℝ) :
    liftReal f (SpecialLinearGroup.mapGL ℝ σ * binaryUnipotent (y + 3) * r) =
      liftReal f (SpecialLinearGroup.mapGL ℝ σ * binaryUnipotent y * r) := by
  have hpos : 0 < (GeneralLinearGroup.det
      (SpecialLinearGroup.mapGL ℝ σ * binaryUnipotent y * r) : ℝˣ).val := by
    rw [det_mapGL_unipotent_mul]
    exact hr
  have hmul : SpecialLinearGroup.mapGL ℝ σ * binaryUnipotent (y + 3) * r =
      SpecialLinearGroup.mapGL ℝ (σ * T3 * σ⁻¹) *
        (SpecialLinearGroup.mapGL ℝ σ * binaryUnipotent y * r) := by
    rw [map_mul, map_mul, map_inv, mapGL_T3, add_comm y 3,
      BinaryStrongApproximation.unipotent_add]
    group
  rw [hmul]
  exact liftReal_gamma1 f _ (conj_T3_mem σ) _ hpos

/-! ### Continuity and the vanishing integral -/

theorem continuous_vadd_upperHalfPlane (z : UpperHalfPlane) :
    Continuous (fun y : ℝ => y +ᵥ z) := by
  refine continuous_induced_rng.2 ?_
  have h : (UpperHalfPlane.coe ∘ fun y : ℝ => y +ᵥ z) = fun y : ℝ => ((y : ℂ) + (z : ℂ)) := by
    funext y
    simp [UpperHalfPlane.coe_vadd]
  rw [h]
  fun_prop

theorem continuous_slash_mapGL {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (g : BinaryRealGL) : Continuous (⇑f ∣[k] g) :=
  (ModularFormClass.holo (CuspForm.translate f g)).continuous

theorem continuous_liftReal_unipotent {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (σ : SpecialLinearGroup (Fin 2) ℤ) (r : BinaryRealGL)
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    Continuous (fun y : ℝ =>
      liftReal f (SpecialLinearGroup.mapGL ℝ σ * binaryUnipotent y * r)) := by
  simp_rw [liftReal_unipotent_eq f σ r hr]
  exact continuous_const.mul
    ((continuous_slash_mapGL f (SpecialLinearGroup.mapGL ℝ σ)).comp
      (continuous_vadd_upperHalfPlane _))

theorem three_mem_strictPeriods (σ : SpecialLinearGroup (Fin 2) ℤ) :
    (3 : ℝ) ∈ (ConjAct.toConjAct (SpecialLinearGroup.mapGL ℝ σ)⁻¹ •
      binaryRealGammaOneThree).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have h3 : Matrix.GeneralLinearGroup.upperRightHom (3 : ℝ) = binaryUnipotent (3 : ℝ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.upperRightHom_apply, binaryUnipotent]
  have e : ∀ g : BinaryRealGL, (ConjAct.toConjAct g⁻¹)⁻¹ = ConjAct.toConjAct g := fun g => by
    rw [← map_inv, inv_inv]
  rw [e, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, h3, ← mapGL_T3]
  exact ⟨σ * T3 * σ⁻¹, conj_T3_mem σ, by rw [map_mul, map_mul, map_inv]⟩

theorem coe_translate_eq {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (g : BinaryRealGL) :
    ⇑(CuspForm.translate f g) = ⇑f ∣[k] g := rfl

theorem integral_translate_zero {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (σ : SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t) :
    ∫ u in (0 : ℝ)..3, (⇑f ∣[k] SpecialLinearGroup.mapGL ℝ σ)
      ⟨(u : ℂ) + t * Complex.I, by simpa using ht⟩ = 0 := by
  have hper := three_mem_strictPeriods σ
  have h0 := ModularFormClass.qExpansion_coeff_eq_intervalIntegral
    (f := CuspForm.translate f (SpecialLinearGroup.mapGL ℝ σ)) (h := 3) (by norm_num) hper 0 ht
  rw [CuspFormClass.qExpansion_coeff_zero
    (f := CuspForm.translate f (SpecialLinearGroup.mapGL ℝ σ)) (by norm_num) hper] at h0
  have h1 := h0.symm
  simp only [pow_zero, div_one, one_mul] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · norm_num at h
  · exact h

theorem vadd_mk_eq (u t : ℝ) (ht : 0 < t) :
    u +ᵥ (⟨(t : ℂ) * Complex.I, by simpa using ht⟩ : UpperHalfPlane) =
      ⟨(u : ℂ) + t * Complex.I, by simpa using ht⟩ := by
  ext
  rw [UpperHalfPlane.coe_vadd]

theorem integral_vadd_slash_zero {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (σ : SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t) :
    ∫ u in (0 : ℝ)..3, (⇑f ∣[k] SpecialLinearGroup.mapGL ℝ σ)
      (u +ᵥ (⟨(t : ℂ) * Complex.I, by simpa using ht⟩ : UpperHalfPlane)) = 0 := by
  simp_rw [vadd_mk_eq _ t ht]
  exact integral_translate_zero f σ t ht

theorem integral_slash_vadd_zero {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (σ : SpecialLinearGroup (Fin 2) ℤ) (z0 : UpperHalfPlane) :
    ∫ y in (0 : ℝ)..3, (⇑f ∣[k] SpecialLinearGroup.mapGL ℝ σ) (y +ᵥ z0) = 0 := by
  have hper := three_mem_strictPeriods σ
  obtain ⟨w0, hw0⟩ : ∃ w0 : UpperHalfPlane,
      w0 = ⟨(z0.im : ℂ) * Complex.I, by simpa using z0.im_pos⟩ := ⟨_, rfl⟩
  have hz0eq : ∀ y : ℝ, y +ᵥ z0 = (y + (z0 : ℂ).re) +ᵥ w0 := by
    intro y
    ext
    rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd, hw0]
    refine Complex.ext ?_ ?_ <;> simp
  have hperG : Function.Periodic
      (fun u : ℝ => (⇑f ∣[k] SpecialLinearGroup.mapGL ℝ σ) (u +ᵥ w0)) 3 := by
    intro u
    have h := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods
      (CuspForm.translate f (SpecialLinearGroup.mapGL ℝ σ)) (u +ᵥ w0) hper
    show (⇑f ∣[k] SpecialLinearGroup.mapGL ℝ σ) ((u + 3) +ᵥ w0) =
      (⇑f ∣[k] SpecialLinearGroup.mapGL ℝ σ) (u +ᵥ w0)
    rw [add_comm u 3, add_vadd]
    exact h
  have hzero := integral_vadd_slash_zero f σ z0.im z0.im_pos
  rw [← hw0] at hzero
  simp_rw [hz0eq]
  have hshift := intervalIntegral.integral_comp_add_right
    (fun u : ℝ => (⇑f ∣[k] SpecialLinearGroup.mapGL ℝ σ) (u +ᵥ w0)) (a := 0) (b := 3)
    (z0 : ℂ).re
  have hperiod := hperG.intervalIntegral_add_eq ((0 : ℝ) + (z0 : ℂ).re) 0
  rw [hshift]
  rw [zero_add, zero_add] at hperiod
  rw [show ((3 : ℝ) + (z0 : ℂ).re) = (z0 : ℂ).re + 3 by ring, zero_add, hperiod, hzero]

theorem integral_liftReal_unipotent {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (σ : SpecialLinearGroup (Fin 2) ℤ) (r : BinaryRealGL)
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    ∫ y in (0 : ℝ)..3, liftReal f (SpecialLinearGroup.mapGL ℝ σ * binaryUnipotent y * r) = 0 := by
  simp_rw [liftReal_unipotent_eq f σ r hr]
  rw [intervalIntegral.integral_const_mul, integral_slash_vadd_zero, mul_zero]

end TernaryPeriodPolynomials.CuspIntegral
