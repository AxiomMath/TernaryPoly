module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ESSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SymFixed

@[expose] public section


/-!
# Period cocycles of cusp forms are trivial on parabolic elements (analytic core)

Paper: Lemma C.3
(`ar:lem:seed`): the seeds of cusp forms lie in the mixed cuspidal group `𝒞_P`.

Let `f` be a cusp form of weight `n + 3` for the image of a subgroup `Λ ⊆ SL₂(ℤ)`, `γ ∈ Λ`,
`g ∈ SL₂(ℤ)` and `γ g = g δ` with `δ = ±T^k`, `k ≠ 0`, so that `γ` fixes the cusp `g · ∞`. The
Eichler cocycle `ε_f(γ)`, evaluated at the first column of `g`, vanishes
(`eval_eps_zero_of_cusp`): the function `H(w) = P_v(g w)` has the constant translation defect
`H(w + k) - H(w) = ε_f(γ)(v)`, its derivative is `± (f ∣ g)(w)`
(`integrand_cusp_eq`), which tends to `0` at `i∞` because `f` vanishes at the cusp, and a
constant translation defect of a primitive of a function tending to `0` is `0`
(`period_defect_eq_zero`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups ModularForm
open GeneralEisenstein Matrix MvPolynomial UpperHalfPlane
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.LevelThree

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

theorem slash_mapGL_apply (f : ℍ → ℂ) (κ : ℤ) (g : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[κ] (SpecialLinearGroup.mapGL ℝ g)) τ =
      f (SpecialLinearGroup.mapGL ℝ g • τ) * (dnm (SpecialLinearGroup.mapGL ℝ g) τ) ^ (-κ) :=
  ModularForm.SL_slash_apply (f := f) (k := κ) g τ


theorem invCoord_eq_of_comm (γ g δ : SL(2, ℤ)) (k σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![σ, σ * k; 0, σ]) (hcomm : γ * g = g * δ) :
    invCoord (SpecialLinearGroup.mapGL ℝ γ)
        ![((g 0 0 : ℤ) : ℂ), ((g 1 0 : ℤ) : ℂ)] =
      (σ : ℂ) • ![((g 0 0 : ℤ) : ℂ), ((g 1 0 : ℤ) : ℂ)] := by
  have hc := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ)) hcomm
  simp only [Matrix.SpecialLinearGroup.coe_mul, hδ] at hc
  have e1 := congrFun (congrFun hc 0) 0
  have e2 := congrFun (congrFun hc 1) 0
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e1 e2
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have h1 : (γ 1 1 : ℤ) * g 0 0 - γ 0 1 * g 1 0 = σ * g 0 0 := by
    have h : σ * ((γ 1 1 : ℤ) * g 0 0 - γ 0 1 * g 1 0 - σ * g 0 0) = 0 := by
      linear_combination (g 0 0 : ℤ) * hdet - (γ 1 1 : ℤ) * e1 + (γ 0 1 : ℤ) * e2 -
        (g 0 0 : ℤ) * hσ2
    rcases hσ with rfl | rfl <;> simp at h <;> linarith
  have h2 : -(γ 1 0 : ℤ) * g 0 0 + γ 0 0 * g 1 0 = σ * g 1 0 := by
    have h : σ * (-(γ 1 0 : ℤ) * g 0 0 + γ 0 0 * g 1 0 - σ * g 1 0) = 0 := by
      linear_combination (g 1 0 : ℤ) * hdet + (γ 1 0 : ℤ) * e1 - (γ 0 0 : ℤ) * e2 -
        (g 1 0 : ℤ) * hσ2
    rcases hσ with rfl | rfl <;> simp at h <;> linarith
  funext i
  fin_cases i
  · simp only [invCoord, SpecialLinearGroup.mapGL]
    simpa using congrArg (fun z : ℤ => (z : ℂ)) h1
  · simp only [invCoord, SpecialLinearGroup.mapGL]
    simpa using congrArg (fun z : ℤ => (z : ℂ)) h2

/-- **A constant translation defect of a primitive of a function decaying at `i∞` is zero.** -/
theorem period_defect_eq_zero (H Φ : ℂ → ℂ) (k : ℤ) (C : ℂ)
    (hH : ∀ w : ℂ, 0 < w.im → HasDerivAt H (Φ w) w)
    (hper : ∀ w : ℂ, 0 < w.im → H (w + k) - H w = C)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ w : ℂ, A ≤ w.im → ‖Φ w‖ < ε) : C = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖C‖ ≤ ε * |(k : ℝ)| := by
    intro ε hε
    obtain ⟨A, hA⟩ := hdecay ε hε
    set y : ℝ := max A 1 with hy
    have hypos : 0 < y := lt_of_lt_of_le one_pos (le_max_right _ _)
    set w₀ : ℂ := ⟨0, y⟩ with hw₀
    have him : ∀ t : ℝ, (w₀ + (t : ℂ) * (k : ℂ)).im = y := by
      intro t
      simp [hw₀]
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => H (w₀ + (s : ℂ) * (k : ℂ)))
        (Φ (w₀ + (t : ℂ) * (k : ℂ)) * (k : ℂ)) t := by
      intro t
      have h1 : HasDerivAt (fun z : ℂ => w₀ + z * (k : ℂ)) (k : ℂ) (t : ℂ) := by
        simpa using ((hasDerivAt_id (t : ℂ)).mul_const (k : ℂ)).const_add w₀
      have h2 := (hH (w₀ + (t : ℂ) * (k : ℂ)) (by rw [him]; exact hypos)).comp (t : ℂ) h1
      exact h2.comp_ofReal
    have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s : ℝ => H (w₀ + (s : ℂ) * (k : ℂ)))
      (f' := fun t : ℝ => Φ (w₀ + (t : ℂ) * (k : ℂ)) * (k : ℂ)) (C := ε * |(k : ℝ)|)
      (a := 0) (b := 1)
      (fun t _ => (hderiv t).hasDerivWithinAt) (fun t _ => by
        rw [norm_mul]
        have : ‖Φ (w₀ + (t : ℂ) * (k : ℂ))‖ < ε := hA _ (by rw [him]; exact le_max_left _ _)
        have hk : ‖(k : ℂ)‖ = |(k : ℝ)| := by simp
        rw [hk]
        exact mul_le_mul_of_nonneg_right this.le (abs_nonneg _)) 1 (by simp)
    have hC : H (w₀ + (1 : ℝ) * (k : ℂ)) - H (w₀ + (0 : ℝ) * (k : ℂ)) = C := by
      have := hper w₀ (by simp [hw₀, hypos])
      simpa using this
    rw [hC] at hbound
    simpa using hbound
  by_contra hne
  have hpos : 0 < ‖C‖ := norm_pos_iff.mpr hne
  have := key (‖C‖ / (2 * (|(k : ℝ)| + 1))) (by positivity)
  have hk0 : 0 ≤ |(k : ℝ)| := abs_nonneg _
  have : ‖C‖ ≤ ‖C‖ / (2 * (|(k : ℝ)| + 1)) * |(k : ℝ)| := this
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith



/-- The Möbius action of `δ = σ T^k` is the translation by `k`. -/
theorem mob_pm_T (δ : SL(2, ℤ)) (k σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![σ, σ * k; 0, σ]) (w : ℂ) :
    mob (SpecialLinearGroup.mapGL ℝ δ) w = w + k := by
  have hσ0 : (σ : ℝ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have e00 : ((δ 0 0 : ℤ) : ℝ) = σ := by
    rw [show δ 0 0 = σ from by simpa using congrFun (congrFun hδ 0) 0]
  have e01 : ((δ 0 1 : ℤ) : ℝ) = σ * k := by
    rw [show δ 0 1 = σ * k from by simpa using congrFun (congrFun hδ 0) 1]; push_cast; ring
  have e10 : ((δ 1 0 : ℤ) : ℝ) = 0 := by
    rw [show δ 1 0 = 0 from by simpa using congrFun (congrFun hδ 1) 0]; simp
  have e11 : ((δ 1 1 : ℤ) : ℝ) = σ := by
    rw [show δ 1 1 = σ from by simpa using congrFun (congrFun hδ 1) 1]
  have hm : ∀ i j, ((SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) i j : ℝ) = ((δ i j : ℤ) : ℝ) :=
    fun i j => rfl
  unfold mob
  rw [hm, hm, hm, hm, e00, e01, e10, e11]
  push_cast
  have hσc : ((σ : ℤ) : ℂ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  field_simp
  simp only [mul_zero, zero_add]
  field_simp


theorem aux_div_mul (N D c a : ℂ) (hD : D ≠ 0) : (N / D * c - a) * D = N * c - a * D := by
  field_simp

/-- The derivative of the primitive along the cusp `g · ∞` is the slashed cusp form. -/
theorem integrand_cusp_eq (n : ℕ) (f : ℍ → ℂ) (g : SL(2, ℤ)) (w : ℂ) (hw : 0 < w.im) :
    binaryIntegrand n (fun z => f (ofComplex z))
        ![((g 0 0 : ℤ) : ℂ), ((g 1 0 : ℤ) : ℂ)] (mob (SpecialLinearGroup.mapGL ℝ g) w) *
      (1 / dnm (SpecialLinearGroup.mapGL ℝ g) w ^ 2) =
    (-1 : ℂ) ^ (n + 1) *
      (f ∣[((n + 3 : ℕ) : ℤ)] (SpecialLinearGroup.mapGL ℝ g)) ⟨w, hw⟩ := by
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hdetc : ((g 0 0 : ℤ) : ℂ) * (g 1 1 : ℤ) - ((g 0 1 : ℤ) : ℂ) * (g 1 0 : ℤ) = 1 := by
    exact_mod_cast hdet
  have hden : dnm (SpecialLinearGroup.mapGL ℝ g) w ≠ 0 := dnm_ne_zero _ hw
  have hm : ∀ i j, ((SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j : ℝ) = ((g i j : ℤ) : ℝ) :=
    fun i j => rfl
  have hpos : 0 < (SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ).det.val := by
    simp [SpecialLinearGroup.mapGL]
  have hmob := mob_eq_smul (SpecialLinearGroup.mapGL ℝ g) hpos ⟨w, hw⟩
  rw [slash_mapGL_apply]
  have hD : ((g 1 0 : ℤ) : ℂ) * w + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
    unfold dnm at hden
    rw [hm, hm] at hden
    push_cast at hden
    exact hden
  have hdn : dnm (SpecialLinearGroup.mapGL ℝ g) w = ((g 1 0 : ℤ) : ℂ) * w + ((g 1 1 : ℤ) : ℂ) := by
    unfold dnm
    rw [hm, hm]
    push_cast
    rfl
  have e : mob (SpecialLinearGroup.mapGL ℝ g) w * ((g 1 0 : ℤ) : ℂ) - ((g 0 0 : ℤ) : ℂ) =
      -1 / dnm (SpecialLinearGroup.mapGL ℝ g) w := by
    rw [hdn, eq_div_iff hD]
    unfold mob
    rw [hm, hm, hm, hm]
    simp only [Complex.ofReal_intCast]
    rw [aux_div_mul _ _ _ _ hD]
    linear_combination (-1 : ℂ) * hdetc
  have hmob' : mob (SpecialLinearGroup.mapGL ℝ g) w =
      (((SpecialLinearGroup.mapGL ℝ g • (⟨w, hw⟩ : ℍ)) : ℍ) : ℂ) := hmob
  unfold binaryIntegrand
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [e, div_pow, hmob', ofComplex_apply, _root_.zpow_neg, zpow_natCast]
  have hn3 : dnm (SpecialLinearGroup.mapGL ℝ g) w ^ (n + 3) =
      dnm (SpecialLinearGroup.mapGL ℝ g) w ^ (n + 1) *
        dnm (SpecialLinearGroup.mapGL ℝ g) w ^ 2 := by
    ring
  rw [show ((n + 3 : ℕ) : ℕ) = n + 3 from rfl, hn3]
  field_simp


theorem eval_eps_zero_of_cusp {Λ : Subgroup SL(2, ℤ)} {n : ℕ}
    (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) (γ g δ : SL(2, ℤ)) (hγ : γ ∈ Λ) (k σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![σ, σ * k; 0, σ])
    (hcomm : γ * g = g * δ) (hm : σ ^ (n + 1) = 1)
    (hzero : IsZeroAtImInfty (⇑f ∣[((n + 3 : ℕ) : ℤ)] (SpecialLinearGroup.mapGL ℝ g))) :
    MvPolynomial.eval ![((g 0 0 : ℤ) : ℂ), ((g 1 0 : ℤ) : ℂ)]
      (eichlerCocycle n (momentPrim (LamGL Λ) n f) (SpecialLinearGroup.mapGL ℝ γ)) = 0 := by
  classical
  set G := momentPrim (LamGL Λ) n f with hG
  set hh : ℂ → ℂ := fun z => f (ofComplex z) with hhh
  set v : Fin 2 → ℂ := ![((g 0 0 : ℤ) : ℂ), ((g 1 0 : ℤ) : ℂ)] with hv
  have hdet : ∀ s : SL(2, ℤ), (SpecialLinearGroup.mapGL ℝ s).det = 1 :=
    fun s => SpecialLinearGroup.det_mapGL s
  have hpos : ∀ s : SL(2, ℤ), 0 < (SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ).det.val :=
    fun s => by simp [hdet s]
  have hγmem : SpecialLinearGroup.mapGL ℝ γ ∈ LamGL Λ := ⟨γ, hγ, rfl⟩
  have hmod : ∀ z : ℂ, 0 < z.im → hh (mob (SpecialLinearGroup.mapGL ℝ γ) z) =
      dnm (SpecialLinearGroup.mapGL ℝ γ) z ^ (n + 3) * hh z := fun z hz =>
    modular_of_slashInvariant (LamGL Λ) (n + 3) f _ hγmem z hz
  have hF : ∀ (w : Fin 2 → ℂ) (z : ℂ), 0 < z.im →
      HasDerivAt (fun x => MvPolynomial.eval w (eichlerPoly n G x)) (binaryIntegrand n hh w z) z :=
    fun w z hz => eichlerPoly_hasDerivAt n hh G (momentPrim_hasDerivAt (LamGL Λ) n f) w hz
  have hI : 0 < (Complex.I : ℂ).im := by simp
  have hC : ∀ z : ℂ, 0 < z.im →
      MvPolynomial.eval v (eichlerCocycle n G (SpecialLinearGroup.mapGL ℝ γ)) =
        MvPolynomial.eval v (eichlerPoly n G (mob (SpecialLinearGroup.mapGL ℝ γ) z)) -
          MvPolynomial.eval (invCoord (SpecialLinearGroup.mapGL ℝ γ) v) (eichlerPoly n G z) := by
    intro z hz
    rw [eval_eichlerCocycle n G (momentPrim_zero (LamGL Λ) n f) (SpecialLinearGroup.mapGL ℝ γ) v]
    unfold periodConst
    exact primitive_defect_const n hh (SpecialLinearGroup.mapGL ℝ γ) (hdet γ) hmod
      (fun w x => MvPolynomial.eval w (eichlerPoly n G x)) hF v hI hz
  have hinv := invCoord_eq_of_comm γ g δ k σ hσ hδ hcomm
  have hscale : ∀ z : ℂ, MvPolynomial.eval (invCoord (SpecialLinearGroup.mapGL ℝ γ) v)
      (eichlerPoly n G z) = MvPolynomial.eval v (eichlerPoly n G z) := by
    intro z
    rw [hinv, SymFixed.eval_smul_of_homogeneous (eichlerPoly_isHomogeneous n G z) (σ : ℂ) v]
    have hmc : (σ : ℂ) ^ (n + 1) = 1 := by exact_mod_cast hm
    rw [hmc, one_mul]
  have hcomm' : SpecialLinearGroup.mapGL ℝ γ * SpecialLinearGroup.mapGL ℝ g =
      SpecialLinearGroup.mapGL ℝ g * SpecialLinearGroup.mapGL ℝ δ := by
    rw [← map_mul, ← map_mul, hcomm]
  set C := MvPolynomial.eval v (eichlerCocycle n G (SpecialLinearGroup.mapGL ℝ γ)) with hCdef
  set H : ℂ → ℂ := fun w => MvPolynomial.eval v
    (eichlerPoly n G (mob (SpecialLinearGroup.mapGL ℝ g) w)) with hH
  have hper : ∀ w : ℂ, 0 < w.im → H (w + k) - H w = C := by
    intro w hw
    have hz : 0 < (mob (SpecialLinearGroup.mapGL ℝ g) w).im :=
      mob_im_pos _ (hpos g) hw
    have h1 := hC _ hz
    rw [hscale] at h1
    have h2 : mob (SpecialLinearGroup.mapGL ℝ γ) (mob (SpecialLinearGroup.mapGL ℝ g) w) =
        mob (SpecialLinearGroup.mapGL ℝ g) (w + k) := by
      rw [← mob_mul _ _ (hdet γ) (hdet g) hw, hcomm',
        mob_mul _ _ (hdet g) (hdet δ) hw, mob_pm_T δ k σ hσ hδ w]
    rw [h2] at h1
    simp only [hH]
    linear_combination -h1
  have hHd : ∀ w : ℂ, 0 < w.im → HasDerivAt H
      (binaryIntegrand n hh v (mob (SpecialLinearGroup.mapGL ℝ g) w) *
        (1 / dnm (SpecialLinearGroup.mapGL ℝ g) w ^ 2)) w := by
    intro w hw
    exact (hF v _ (mob_im_pos _ (hpos g) hw)).comp w (mob_hasDerivAt _ (hdet g) hw)
  have hdecay : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ w : ℂ, A ≤ w.im →
      ‖binaryIntegrand n hh v (mob (SpecialLinearGroup.mapGL ℝ g) w) *
        (1 / dnm (SpecialLinearGroup.mapGL ℝ g) w ^ 2)‖ < ε := by
    intro ε hε
    have h0 := Metric.tendsto_nhds.1 hzero ε hε
    obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 h0
    refine ⟨max A 1, fun w hw => ?_⟩
    have hwpos : 0 < w.im := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hw)
    have h3 := hA ⟨w, hwpos⟩ (le_trans (le_max_left _ _) hw)
    rw [integrand_cusp_eq n f g w hwpos]
    simpa [norm_mul] using h3
  exact period_defect_eq_zero H _ k C hHd hper hdecay

end TernaryPeriodPolynomials.Argument.SeedC3S4c
