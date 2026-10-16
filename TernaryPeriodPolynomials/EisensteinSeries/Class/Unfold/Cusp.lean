module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Series
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Instance

@[expose] public section


/-!
# Cuspidality along a unipotent orbit (the zero Fourier mode on the horocycle)

Paper: "the binary root
average is zero by cuspidality ... Its remaining `u`-dependence is `h(u + iv)`, whose average over the
cusp width is zero".

`integral_unipConj_zero`: for `B ∈ SL₂(ℤ)`, `μ ∈ NZ`, `μ ≠ 0`, and a cusp form `f` of level `Γ(N)`, the
integral over `s ∈ [0, 1]` of the twisted slash of `f` by the unipotent `B⁻¹ [[1, μ s], [0, 1]] B` vanishes
at every point of the upper half-plane. Proof: `slashTwisted` is a cocycle on real matrices
(`slashTwisted_mul`), so the integrand is a constant times `(f ∣ B⁻¹)(z₀ + μ s)`; `f ∣ B⁻¹` is holomorphic,
`N`-periodic (normality of `Γ(N)`) and decays at `i∞` (`CuspFormClass.zero_at_infty_slash`); a
holomorphic periodic function decaying at `i∞` has vanishing horizontal integrals over a period
(`horizontal_integral_zero`: independence of the height by Cauchy's theorem on rectangles and periodicity of
the vertical sides, then the limit `y → ∞`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
open MeasureTheory Set Complex intervalIntegral
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

/-- A holomorphic function on the upper half-plane with period `P` and uniform decay at `i∞` has
vanishing horizontal integrals over one period. -/
theorem horizontal_integral_zero (G : ℂ → ℂ) (P : ℝ)
    (hhol : DifferentiableOn ℂ G {z : ℂ | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → G (z + P) = G z)
    (hdecay : ∀ ε > 0, ∃ A : ℝ, ∀ z : ℂ, A ≤ z.im → ‖G z‖ ≤ ε) (y : ℝ) (hy : 0 < y) :
    ∫ x in (0 : ℝ)..P, G (x + y * I) = 0 := by
  set J : ℝ → ℂ := fun y => ∫ x in (0 : ℝ)..P, G (x + y * I) with hJ
  have hconst : ∀ y1 y2 : ℝ, 0 < y1 → 0 < y2 → J y1 = J y2 := by
    intro y1 y2 h1 h2
    have hsub : (Set.uIcc ((0 + y1 * I : ℂ).re) ((P + y2 * I : ℂ).re)) ×ℂ
        (Set.uIcc ((0 + y1 * I : ℂ).im) ((P + y2 * I : ℂ).im)) ⊆ {z : ℂ | 0 < z.im} := by
      rintro z ⟨-, hz⟩
      simp only [mem_preimage, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
        add_zero, zero_add, mul_one] at hz
      show 0 < z.im
      rcases le_total y1 y2 with h | h
      · rw [uIcc_of_le h] at hz; exact lt_of_lt_of_le h1 hz.1
      · rw [uIcc_of_ge h] at hz; exact lt_of_lt_of_le h2 hz.1
    have := integral_boundary_rect_eq_zero_of_differentiableOn G (0 + y1 * I) (P + y2 * I)
      (hhol.mono hsub)
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, add_zero,
      sub_zero, zero_add, mul_one, add_im, mul_im] at this
    have hv : (∫ y in y1..y2, G ((P : ℂ) + y * I)) = ∫ y in y1..y2, G (((0 : ℝ) : ℂ) + y * I) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht0 : 0 < t := by
        rcases le_total y1 y2 with h | h
        · rw [uIcc_of_le h] at ht; exact lt_of_lt_of_le h1 ht.1
        · rw [uIcc_of_ge h] at ht; exact lt_of_lt_of_le h2 ht.1
      have := hper (t * I) (by simpa using ht0)
      simp only [ofReal_zero, zero_add]
      rw [add_comm]; exact this
    rw [hv] at this
    have h3 : J y1 - J y2 = 0 := by
      simpa [hJ] using this
    exact sub_eq_zero.mp h3
  -- the constant value is zero
  by_contra hne
  have hpos : 0 < ‖J y‖ := norm_pos_iff.mpr hne
  obtain ⟨A, hA⟩ := hdecay (‖J y‖ / (2 * (|P| + 1))) (by positivity)
  have hy' : 0 < max A y + 1 := by
    have := le_max_right A y; linarith
  have hJy : J y = J (max A y + 1) := hconst _ _ hy hy'
  have hle : ‖J (max A y + 1)‖ ≤ ‖J y‖ / (2 * (|P| + 1)) * |P| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := P)
      (f := fun x : ℝ => G (x + (max A y + 1 : ℝ) * I)) (C := ‖J y‖ / (2 * (|P| + 1)))
      (fun x _ => hA _ (by
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
          add_zero, zero_add, mul_one]
        have := le_max_left A y
        linarith))
    simpa [hJ, sub_zero] using this
  rw [← hJy] at hle
  have hP0 : 0 ≤ |P| := abs_nonneg P
  have : ‖J y‖ / (2 * (|P| + 1)) * |P| < ‖J y‖ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hpos]
  linarith

/-! ### The twisted slash operator on real matrices -/

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
open UpperHalfPlane

theorem mob_denom_ne (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) (z : ℂ) (hz : 0 < z.im) :
    (A 1 0 : ℂ) * z + A 1 1 ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.im h0
  have h2 := congrArg Complex.re h0
  simp at h1 h2
  have hd : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
  rcases h1 with h1 | h1
  · rw [h1] at h2 hd
    simp at h2
    rw [h2] at hd
    rw [hd] at hA
    simp at hA
  · linarith

theorem mob_im (a b c d : ℝ) (z : ℂ) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im =
      (a * d - b * c) * z.im / Complex.normSq ((c : ℂ) * z + d) := by
  rw [Complex.div_im]
  simp
  ring

theorem mob_im_pos (C : Matrix (Fin 2) (Fin 2) ℝ) (hC : 0 < C.det) (z : ℂ) (hz : 0 < z.im) :
    0 < (((C 0 0 : ℂ) * z + C 0 1) / ((C 1 0 : ℂ) * z + C 1 1)).im := by
  have hne := mob_denom_ne C hC z hz
  rw [mob_im, ← Matrix.det_fin_two]
  have hn : 0 < Complex.normSq ((C 1 0 : ℂ) * z + C 1 1) := Complex.normSq_pos.mpr hne
  positivity

/-- The cocycle law of the twisted slash operator on real matrices of positive determinant. -/
theorem slashTwisted_mul (k : ℕ) (A1 A2 : Matrix (Fin 2) (Fin 2) ℝ) (h1 : 0 < A1.det)
    (h2 : 0 < A2.det) (h : ℂ → ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    slashTwisted k (A1 * A2) h τ = slashTwisted k A2 (slashTwisted k A1 h) τ := by
  have hd2 := mob_denom_ne A2 h2 τ hτ
  set w : ℂ := ((A2 0 0 : ℂ) * τ + A2 0 1) / ((A2 1 0 : ℂ) * τ + A2 1 1) with hw
  have hwim : 0 < w.im := mob_im_pos A2 h2 τ hτ
  have hd1 := mob_denom_ne A1 h1 w hwim
  have hdet : (A1 * A2).det = A1.det * A2.det := Matrix.det_mul A1 A2
  have hpos : 0 < (A1 * A2).det := by rw [hdet]; exact mul_pos h1 h2
  have hd12 := mob_denom_ne (A1 * A2) hpos τ hτ
  have e1 : ((A1 * A2) 1 0 : ℂ) * τ + ((A1 * A2) 1 1 : ℝ) =
      ((A1 1 0 : ℂ) * w + A1 1 1) * ((A2 1 0 : ℂ) * τ + A2 1 1) := by
    rw [hw]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    field_simp
    ring
  have e2 : (((A1 * A2) 0 0 : ℝ) * τ + ((A1 * A2) 0 1 : ℝ)) /
      (((A1 * A2) 1 0 : ℝ) * τ + ((A1 * A2) 1 1 : ℝ)) =
      ((A1 0 0 : ℂ) * w + A1 0 1) / ((A1 1 0 : ℂ) * w + A1 1 1) := by
    rw [e1, hw]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    field_simp
    ring
  unfold slashTwisted
  rw [e2, e1, hdet]
  push_cast
  rw [mul_zpow, mul_pow]
  simp only [← hw]
  ring

theorem slashTwisted_translate (k : ℕ) (x : ℝ) (φ : ℂ → ℂ) (w : ℂ) :
    slashTwisted k !![1, x; 0, 1] φ w = φ (w + x) := by
  unfold slashTwisted
  simp

theorem det_castSL (γ : SL(2, ℤ)) :
    ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)).det = 1 := by
  have h := RingHom.map_det (Int.castRingHom ℝ) (γ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [Matrix.SpecialLinearGroup.det_coe] at h
  simpa using h.symm

/-- The twisted slash by an `SL₂(ℤ)` matrix is the Mathlib slash of the cusp form. -/
theorem slashTwisted_SL (N n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (γ : SL(2, ℤ))
    (z : ℍ) :
    slashTwisted (n + 3) ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) (hfun f) (z : ℂ) =
      ((⇑f : ℍ → ℂ) ∣[((n + 3 : ℕ) : ℤ)] γ) z := by
  rw [ModularForm.SL_slash_apply]
  have h1 : ((γ • z : ℍ) : ℂ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) * (z : ℂ) +
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ)) / (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * (z : ℂ) +
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)) := by
    simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom, UpperHalfPlane.σ]
  have h2 : UpperHalfPlane.denom γ z = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * (z : ℂ) +
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)) := by
    simp [UpperHalfPlane.denom]
  unfold slashTwisted hfun
  rw [det_castSL, h2]
  simp only [Matrix.map_apply, Int.coe_castRingHom]
  rw [← h1, UpperHalfPlane.ofComplex_apply]
  simp
  ring

/-- The conjugate of a translation by `B ∈ SL₂(ℤ)`. -/
def unipConj (B : SL(2, ℤ)) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) * !![1, x; 0, 1] *
    (B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)

theorem unipConj_eq (B : SL(2, ℤ)) (x : ℝ) :
    unipConj B x = 1 + x • (((B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) *
      !![0, 1; 0, 0] * (B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) := by
  have h1 : (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 1 + x • !![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h2 : ((B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) *
      (B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) = 1 := by
    rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    simp
  unfold unipConj
  rw [h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem denom_SL (γ : SL(2, ℤ)) (z : ℍ) : UpperHalfPlane.denom γ z =
    (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * (z : ℂ) + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)) := by
  simp [UpperHalfPlane.denom]

theorem slash_Tzpow (g : ℍ → ℂ) (k : ℤ) (z : ℍ) (m : ℤ) :
    (g ∣[k] (ModularGroup.T ^ m)) z = g ((m : ℝ) +ᵥ z) := by
  rw [ModularForm.SL_slash_apply, modular_T_zpow_smul]
  have e : ((ModularGroup.T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, m; 0, 1] :=
    ModularGroup.coe_T_zpow m
  have h10 : ((ModularGroup.T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    rw [e]; rfl
  have h11 : ((ModularGroup.T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    rw [e]; rfl
  have hd : UpperHalfPlane.denom (ModularGroup.T ^ m : SL(2, ℤ)) z = 1 := by
    rw [denom_SL, h10, h11]
    simp
  rw [hd]
  simp

theorem slashInv_period (N n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (B : SL(2, ℤ)) (z : ℍ) :
    ((⇑f : ℍ → ℂ) ∣[((n + 3 : ℕ) : ℤ)] B⁻¹) ((N : ℝ) +ᵥ z) = ((⇑f : ℍ → ℂ) ∣[((n + 3 : ℕ) : ℤ)] B⁻¹) z := by
  have h1 : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    have := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
    simpa using this
  have h2 : B⁻¹ * ModularGroup.T ^ (N : ℤ) * B⁻¹⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (CongruenceSubgroup.Gamma_normal N).conj_mem _ h1 _
  have h3 : (⇑f : ℍ → ℂ) ∣[((n + 3 : ℕ) : ℤ)] (B⁻¹ * ModularGroup.T ^ (N : ℤ) * B⁻¹⁻¹) = ⇑f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ h2)
  have h4 : ((⇑f : ℍ → ℂ) ∣[((n + 3 : ℕ) : ℤ)] B⁻¹) ∣[((n + 3 : ℕ) : ℤ)] (ModularGroup.T ^ (N : ℤ)) =
      (⇑f : ℍ → ℂ) ∣[((n + 3 : ℕ) : ℤ)] B⁻¹ := by
    rw [← SlashAction.slash_mul]
    have : B⁻¹ * ModularGroup.T ^ (N : ℤ) = (B⁻¹ * ModularGroup.T ^ (N : ℤ) * B⁻¹⁻¹) * B⁻¹ := by group
    rw [this, SlashAction.slash_mul, h3]
  have := congrFun h4 z
  rw [slash_Tzpow] at this
  simpa using this

/-- The formula for the twisted slash by a conjugated translation: the translation parameter enters
only through `h|B⁻¹` evaluated at the translated Möbius image. -/
theorem slashTwisted_unipConj (k : ℕ) (h : ℂ → ℂ) (B : SL(2, ℤ)) (x : ℝ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    slashTwisted k (unipConj B x) h τ =
      (((B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)).det : ℂ) ^ k *
        ((((B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) 1 0 : ℂ) * τ +
          ((B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) 1 1) ^ (-(k : ℤ)) *
        slashTwisted k (((B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) h
          ((((B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) 0 0 * τ +
            ((B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) 0 1) /
            (((B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) 1 0 * τ +
            ((B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) 1 1) + x) := by
  set Bc := (B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) with hBc
  set Bic := ((B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) with hBic
  have hBc : 0 < Bc.det := by rw [det_castSL]; exact one_pos
  have hBic : 0 < Bic.det := by rw [det_castSL]; exact one_pos
  have hT : (0 : ℝ) < (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp [Matrix.det_fin_two]
  have hBicT : 0 < (Bic * !![1, x; 0, 1]).det := by
    rw [Matrix.det_mul]; exact mul_pos hBic hT
  unfold unipConj
  rw [slashTwisted_mul k (Bic * !![1, x; 0, 1]) Bc hBicT hBc h hτ]
  have hw0 : 0 < ((((Bc 0 0 : ℝ) : ℂ) * τ + (Bc 0 1 : ℝ)) / (((Bc 1 0 : ℝ) : ℂ) * τ + (Bc 1 1 : ℝ))).im :=
    mob_im_pos Bc hBc τ hτ
  have hinner := slashTwisted_mul k Bic !![1, x; 0, 1] hBic hT h hw0
  rw [slashTwisted_translate] at hinner
  have hout : slashTwisted k Bc (slashTwisted k (Bic * !![1, x; 0, 1]) h) τ =
      (Bc.det : ℂ) ^ k * (((Bc 1 0 : ℝ) : ℂ) * τ + (Bc 1 1 : ℝ)) ^ (-(k : ℤ)) *
        slashTwisted k (Bic * !![1, x; 0, 1]) h
          ((((Bc 0 0 : ℝ) : ℂ) * τ + (Bc 0 1 : ℝ)) / (((Bc 1 0 : ℝ) : ℂ) * τ + (Bc 1 1 : ℝ))) := rfl
  rw [hout, hinner]

section Main

variable (N n : ℕ) [NeZero N] (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (B : SL(2, ℤ))

/-- The cusp form slashed by `B⁻¹`, extended to `ℂ` by `ofComplex`. -/
def slashedC (z : ℂ) : ℂ := ((⇑f : ℍ → ℂ) ∣[((n + 3 : ℕ) : ℤ)] B⁻¹) (UpperHalfPlane.ofComplex z)

omit [NeZero N] in
theorem slashedC_diff : DifferentiableOn ℂ (slashedC N n f B) {z : ℂ | 0 < z.im} := by
  have := ModularFormClass.holo (CuspForm.translate f (B⁻¹ : SL(2, ℤ)))
  rw [CuspForm.coe_translate] at this
  exact UpperHalfPlane.mdifferentiable_iff.1 this

omit [NeZero N] in
theorem slashedC_period (z : ℂ) (hz : 0 < z.im) :
    slashedC N n f B (z + ((N : ℝ) : ℂ)) = slashedC N n f B z := by
  have hz' : 0 < (z + (N : ℝ)).im := by simpa using hz
  have h1 : UpperHalfPlane.ofComplex (z + ((N : ℝ) : ℂ)) = (N : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    ext
    simp [add_comm]
  unfold slashedC
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, h1]
  exact slashInv_period N n f B ⟨z, hz⟩

theorem slashedC_decay : ∀ ε > 0, ∃ A : ℝ, ∀ z : ℂ, A ≤ z.im → ‖slashedC N n f B z‖ ≤ ε := by
  intro ε hε
  have hzero := CuspFormClass.zero_at_infty_slash f B⁻¹
  have hev := hzero.eventually (Metric.ball_mem_nhds (0 : ℂ) hε)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 hev
  refine ⟨max A 1, fun z hz => ?_⟩
  have hz1 : 0 < z.im := lt_of_lt_of_le one_pos ((le_max_right A 1).trans hz)
  unfold slashedC
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz1]
  have := hA ⟨z, hz1⟩ ((le_max_left A 1).trans hz)
  simp only [Set.mem_ofPred_eq, dist_zero_right] at this
  exact this.le

omit [NeZero N] in
theorem slashedC_eq (w : ℂ) (hw : 0 < w.im) :
    slashTwisted (n + 3) (((B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ))
      (hfun f) w = slashedC N n f B w := by
  have := slashTwisted_SL N n f B⁻¹ ⟨w, hw⟩
  unfold slashedC
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  exact this

/-- **U1: the unipotent-orbit integral of a cusp form vanishes.** For `B ∈ SL₂(ℤ)` and a nonzero
multiple `μ` of the level `N`, the average over one period of the unipotent conjugate
`B⁻¹ [[1, μ s], [0, 1]] B` of the twisted slash of a cusp form of level `Γ(N)` is zero
(cuspidality at the cusp `B⁻¹ ∞`). -/
theorem integral_unipConj_zero (μ : ℤ) (hμ0 : μ ≠ 0) (hμ : (N : ℤ) ∣ μ) (τ : ℂ)
    (hτ : 0 < τ.im) :
    ∫ s in (0 : ℝ)..1, slashTwisted (n + 3) (unipConj B ((μ : ℝ) * s)) (hfun f) τ = 0 := by
  set Bc := (B : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) with hBc
  have hBcd : 0 < Bc.det := by rw [det_castSL]; exact one_pos
  set w0 : ℂ := ((Bc 0 0 : ℝ) * τ + (Bc 0 1 : ℝ)) / ((Bc 1 0 : ℝ) * τ + (Bc 1 1 : ℝ)) with hw0
  have hw0im : 0 < w0.im := mob_im_pos Bc hBcd τ hτ
  set C0 : ℂ := (Bc.det : ℂ) ^ (n + 3) * (((Bc 1 0 : ℝ) : ℂ) * τ + (Bc 1 1 : ℝ)) ^ (-((n + 3 : ℕ) : ℤ))
    with hC0
  have key : ∀ s : ℝ, slashTwisted (n + 3) (unipConj B ((μ : ℝ) * s)) (hfun f) τ =
      C0 * slashedC N n f B (w0 + (((μ : ℝ) * s : ℝ) : ℂ)) := by
    intro s
    rw [slashTwisted_unipConj (n + 3) (hfun f) B ((μ : ℝ) * s) hτ, slashedC_eq N n f B]
    · show 0 < (w0 + (((μ : ℝ) * s : ℝ) : ℂ)).im
      simpa using hw0im
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul]
  suffices h : ∫ s in (0 : ℝ)..1, slashedC N n f B (w0 + (((μ : ℝ) * s : ℝ) : ℂ)) = 0 by
    rw [h, mul_zero]
  -- reduce to a horizontal integral over `μ / N` periods
  set a : ℝ := w0.re with ha
  set b : ℝ := w0.im with hb
  have hbpos : 0 < b := hw0im
  set F : ℝ → ℂ := fun x => slashedC N n f B ((x : ℂ) + (b : ℂ) * Complex.I) with hF
  have hFform : ∀ s : ℝ, slashedC N n f B (w0 + (((μ : ℝ) * s : ℝ) : ℂ)) = F ((μ : ℝ) * s + a) := by
    intro s
    simp only [hF]
    congr 1
    apply Complex.ext <;> simp [ha, hb]; ring
  simp_rw [hFform]
  have hμR : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ0
  rw [intervalIntegral.integral_comp_mul_add F hμR a]
  have hFcont : Continuous F := by
    have := (slashedC_diff N n f B).continuousOn
    refine this.comp_continuous (by fun_prop) (fun x => ?_)
    simp [hbpos]
  have hFper : Function.Periodic F (N : ℝ) := by
    intro x
    simp only [hF]
    have := slashedC_period N n f B ((x : ℂ) + (b : ℂ) * Complex.I) (by simpa using hbpos)
    rw [← this]
    congr 1
    push_cast
    ring
  have hint : ∀ t₁ t₂ : ℝ, IntervalIntegrable F MeasureTheory.volume t₁ t₂ :=
    fun t₁ t₂ => hFcont.intervalIntegrable t₁ t₂
  obtain ⟨ℓ, hℓ⟩ := hμ
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hμeq : (μ : ℝ) = ℓ * N := by
    have : (μ : ℝ) = ((N : ℤ) * ℓ : ℤ) := by exact_mod_cast hℓ
    rw [this]; push_cast; ring
  have hzero := horizontal_integral_zero (slashedC N n f B) (N : ℝ) (slashedC_diff N n f B)
    (fun z hz => slashedC_period N n f B z hz) (slashedC_decay N n f B) b hbpos
  have hI0 : ∫ x in (0 : ℝ)..(N : ℝ), F x = 0 := hzero
  have h1 := hFper.intervalIntegral_add_zsmul_eq ℓ a hint
  have h2 := hFper.intervalIntegral_add_eq a 0
  rw [zero_add] at h2
  have h3 : (μ : ℝ) * 0 + a = a := by ring
  have h4 : (μ : ℝ) * 1 + a = a + ℓ • (N : ℝ) := by
    rw [hμeq]; simp [zsmul_eq_mul]; ring
  rw [h3, h4, h1, h2, hI0]
  simp

end Main

end TernaryPeriodPolynomials.Argument.EisensteinClass
