module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Analytic
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Fourier

@[expose] public section


/-!
# The reproducing formula and injectivity of the realization

The realization of the lowest weight vector `lowestMinus c` (the function `((w - i)^k)⁻¹ • c` on
the lower half plane) is `reproConst k · ε c` (`realizeU_lowestMinus`): after `w ↦ conj w` this
is the reproducing formula of the weighted Bergman space for the holomorphic function
`z ↦ (Im z)^(-k/2) ε c (x · gUp z)`.

For injectivity, let `G` be a regular vector whose rotated realizations all vanish at `x`. By the
b-trick and Parseval, `θ ↦ realizeU (rotGL θ · G) x` is an absolutely convergent trigonometric
series whose coefficient at the frequency `-k` is the realization at `x` of the lowest weight
vector built from `coeffMinus G 0`; so this coefficient vanishes, and by the reproducing
formula and the injectivity of `ε`, `coeffMinus G 0 = (2i)^k G(-i) = 0`. Applying this to all
real translates of a smooth vector with zero realization shows that it vanishes on `ℂ ∖ ℝ`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Complex
open scoped ContDiff InnerProductSpace
open TernaryPeriodPolynomials.Automorphic.SmoothVectors

namespace TernaryPeriodPolynomials.Regularity

/-- The constant `π/(k-1) · 4^(1-k) · (2i)^k` of the reproducing formula. -/
def reproConst (k : ℕ) : ℂ :=
  ((Real.pi / ((k : ℝ) - 1) * (4 : ℝ) ^ (1 - (k : ℝ)) : ℝ) : ℂ) * (2 * I) ^ k

theorem reproConst_ne_zero {k : ℕ} (hk : 2 ≤ k) : reproConst k ≠ 0 := by
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℝ) < Real.pi / ((k : ℝ) - 1) * (4 : ℝ) ^ (1 - (k : ℝ)) :=
    mul_pos (div_pos Real.pi_pos hk1) (by positivity)
  unfold reproConst
  refine mul_ne_zero ?_ (pow_ne_zero _ (mul_ne_zero two_ne_zero I_ne_zero))
  exact_mod_cast hpos.ne'

theorem atInfinity_one_binary : (atInfinity (1 : GL (Fin 2) ℝ) : BinaryAdelicGL) = 1 := by
  rw [atInfinity, combineGL_one]

theorem norm_neg_sq (k n : ℕ) : ‖-(((k : ℂ) + 2 * n) ^ 2)‖ = ((k : ℝ) + 2 * n) ^ 2 := by
  have hc : ((k : ℂ) + 2 * n) = (((k : ℝ) + 2 * n : ℝ) : ℂ) := by push_cast; ring
  rw [norm_neg, norm_pow, hc, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

section Lowest

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The lower lowest weight vector is an eigenvector of the rotations. -/
theorem realRep_rot_lowestMinus (hk : 2 ≤ k) (e : E) (θ : ℝ) :
    realRep k E (rotGL θ) (lowestMinus hk e) = cexp (-((k : ℂ) * θ) * I) • lowestMinus hk e := by
  refine eq_of_coeff hk (fun n => ?_) (fun n => ?_)
  · rw [coeffPlus_realRep_rot, coeffPlus_smul, coeffPlus_lowestMinus, smul_zero, smul_zero]
  · rw [coeffMinus_realRep_rot, coeffMinus_smul, coeffMinus_lowestMinus]
    by_cases hn : n = 0
    · subst hn
      simp
    · simp [hn]

theorem isRotSmooth_lowestMinus (hk : 2 ≤ k) (e : E) : IsRotSmooth (lowestMinus hk e) := by
  unfold IsRotSmooth
  have hfun : (fun θ : ℝ => realRep k E (rotGL θ) (lowestMinus hk e)) =
      fun θ : ℝ => cexp (-((k : ℂ) * θ) * I) • lowestMinus hk e :=
    funext (realRep_rot_lowestMinus hk e)
  rw [hfun]
  have hin : ContDiff ℝ ∞ fun θ : ℝ => -((k : ℂ) * (θ : ℂ)) * I :=
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg).mul contDiff_const
  have hexp : ContDiff ℝ ∞ fun θ : ℝ => cexp (-((k : ℂ) * θ) * I) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).comp hin
  exact hexp.smul (contDiff_const (c := lowestMinus hk e))

omit [CompleteSpace E] in
theorem IsRotSmooth.rot {G : BergmanSpace k E} (hG : IsRotSmooth G) (θ : ℝ) :
    IsRotSmooth (realRep k E (rotGL θ) G) := by
  unfold IsRotSmooth at *
  have hfun : (fun t : ℝ => realRep k E (rotGL t) (realRep k E (rotGL θ) G)) =
      (fun t => realRep k E (rotGL t) G) ∘ (fun t => t + θ) := by
    funext t
    simp only [Function.comp, rotGL_add, map_mul, Module.End.mul_apply]
  rw [hfun]
  exact hG.comp (contDiff_id.add contDiff_const)

/-- `Σ w_n ‖x_n‖ ‖y_n‖` converges for the coefficients of two Bergman vectors. -/
theorem summable_weight_mul_plus (hk : 2 ≤ k) (b V : BergmanSpace k E) :
    Summable fun n => bergmanWeight k n * (‖coeffPlus b n‖ * ‖coeffPlus V n‖) := by
  have hb := (hasSum_norm_sq hk b).summable
  have hV := (hasSum_norm_sq hk V).summable
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (bergmanWeight_pos hk n).le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (fun n => ?_) (hb.add hV)
  have hw := (bergmanWeight_pos hk n).le
  have h1 : ‖coeffPlus b n‖ * ‖coeffPlus V n‖ ≤
      (‖coeffPlus b n‖ ^ 2 + ‖coeffMinus b n‖ ^ 2) + (‖coeffPlus V n‖ ^ 2 + ‖coeffMinus V n‖ ^ 2) :=
    by nlinarith [sq_nonneg (‖coeffPlus b n‖ - ‖coeffPlus V n‖), sq_nonneg ‖coeffMinus b n‖,
      sq_nonneg ‖coeffMinus V n‖]
  have h2 := mul_le_mul_of_nonneg_left h1 hw
  unfold bergmanWeight at h2 ⊢
  linarith

theorem summable_weight_mul_minus (hk : 2 ≤ k) (b V : BergmanSpace k E) :
    Summable fun n => bergmanWeight k n * (‖coeffMinus b n‖ * ‖coeffMinus V n‖) := by
  have hb := (hasSum_norm_sq hk b).summable
  have hV := (hasSum_norm_sq hk V).summable
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (bergmanWeight_pos hk n).le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (fun n => ?_) (hb.add hV)
  have hw := (bergmanWeight_pos hk n).le
  have h1 : ‖coeffMinus b n‖ * ‖coeffMinus V n‖ ≤
      (‖coeffPlus b n‖ ^ 2 + ‖coeffMinus b n‖ ^ 2) + (‖coeffPlus V n‖ ^ 2 + ‖coeffMinus V n‖ ^ 2) :=
    by nlinarith [sq_nonneg (‖coeffMinus b n‖ - ‖coeffMinus V n‖), sq_nonneg ‖coeffPlus b n‖,
      sq_nonneg ‖coeffPlus V n‖]
  have h2 := mul_le_mul_of_nonneg_left h1 hw
  unfold bergmanWeight at h2 ⊢
  linarith

end Lowest

variable {k : ℕ} (M : FiniteModel k)

theorem coeffMinus_mem_fixed {U : Subgroup BinaryFiniteGL} {G : BergmanSpace k M.E}
    (hG : ∀ w, G w ∈ fixedSubmodule M.σ U) (n : ℕ) :
    coeffMinus G n ∈ fixedSubmodule M.σ U := by
  intro u
  have hfix : finRep k M.σ M.unitary u.val G = G :=
    BergmanSpace.ext fun w => by rw [finRep_apply]; exact hG w u
  rw [← coeffMinus_finRep M.σ M.unitary u.val G n, hfix]

theorem lowestMinus_mem_fixed (hk : 2 ≤ k) {U : Subgroup BinaryFiniteGL} {c : M.E}
    (hc : c ∈ fixedSubmodule M.σ U) (w : ℂ) :
    lowestMinus hk c w ∈ fixedSubmodule M.σ U := by
  rw [lowestMinus_apply]
  split_ifs
  · exact Submodule.smul_mem _ _ hc
  · exact Submodule.zero_mem _

/-- **The reproducing formula** for the realization of the lower lowest weight vector. -/
theorem realizeU_lowestMinus (hk : 3 ≤ k) {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    {e : M.E} (he : e ∈ fixedSubmodule M.σ U) (x : BinaryAdelicGL) :
    realizeU M hU (lowestMinus (by omega) e) x =
      reproConst k * M.ε ⟨e, fixed_le_finiteSmooth M hU he⟩ x := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨C, hC⟩ := (M.like ⟨e, fixed_le_finiteSmooth M hU he⟩).bounded
  let h : ℂ → ℂ := fun z => (((z.im ^ ((k : ℝ) / 2))⁻¹ : ℝ) : ℂ) *
    M.ε ⟨e, fixed_le_finiteSmooth M hU he⟩ (x * atInfinity (gUp z))
  have hhol : DifferentiableOn ℂ h upper := M.holomorphic ⟨e, fixed_le_finiteSmooth M hU he⟩ x
  have hCb : ∀ z ∈ upper, ‖h z‖ * z.im ^ ((k : ℝ) / 2) ≤ C := by
    intro z hz
    have hz' : 0 < z.im := hz
    have hp : 0 < z.im ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hz' _
    simp only [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    rw [mul_right_comm, inv_mul_cancel₀ hp.ne', one_mul]
    exact hC _
  have hmp := measurePreserving_conj
  have hmeas := continuousOn_realizeIntegrand M hU (lowestMinus hk2 e) x
  unfold realizeU
  conv_lhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact BergmanAux.aesm hmeas)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := upper) ?_]
  · have hcongr : ∫ z in upper, evalU M hU (x * atInfinity (gBar ((starRingEnd ℂ) z)))
          (lowestMinus hk2 e ((starRingEnd ℂ) z)) *
          ((|((starRingEnd ℂ) z).im| ^ ((k : ℝ) / 2) : ℝ) : ℂ) ∂hypMeasure =
        ∫ z in upper, ((starRingEnd ℂ) (z + I) ^ k)⁻¹ * h z * ((z.im ^ k : ℝ) : ℂ)
          ∂hypMeasure := by
      refine setIntegral_congr_fun measurableSet_upper fun z hz => ?_
      have hz' : 0 < z.im := hz
      have hw : ((starRingEnd ℂ) z).im < 0 := by
        rw [Complex.conj_im]
        linarith
      have hp : 0 < z.im ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hz' _
      have hpC : ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
      have hX : (starRingEnd ℂ) (z + I) ≠ 0 := by
        rw [map_ne_zero]
        intro h0
        have := congrArg Complex.im h0
        simp at this
        linarith
      have hg : gBar ((starRingEnd ℂ) z) = gUp z := by rw [gBar, Complex.conj_conj]
      have him : |((starRingEnd ℂ) z).im| = z.im := by
        rw [Complex.conj_im, abs_neg, abs_of_pos hz']
      have hsub : (starRingEnd ℂ) z - I = (starRingEnd ℂ) (z + I) := by
        rw [map_add, Complex.conj_I, sub_eq_add_neg]
      rw [lowestMinus_apply, ite_eq_left hw, map_smul, smul_eq_mul, evalU_of_mem M hU _ he, hg, him,
        hsub, ← rpow_half_sq hz' k]
      simp only [h]
      push_cast
      field_simp
    rw [hcongr, integral_upper_reproducing hk hhol hCb]
    have hI : h I = M.ε ⟨e, fixed_le_finiteSmooth M hU he⟩ x := by
      simp only [h, Complex.I_im, Real.one_rpow, inv_one, Complex.ofReal_one, one_mul, gUp_I,
        atInfinity_one_binary, mul_one]
    rw [hI, reproConst]
  · intro z hz
    have hz' : ¬ ((starRingEnd ℂ) z).im < 0 := by
      rw [Complex.conj_im]
      have : ¬ 0 < z.im := hz
      exact not_lt.mpr (by linarith [not_lt.mp this])
    rw [lowestMinus_apply, ite_eq_right hz', map_zero, zero_mul]

/-- If all rotated realizations of a regular vector vanish, its lowest lower coefficient
vanishes. -/
theorem coeffMinus_zero_eq_zero (hk : 6 ≤ k) {U : Subgroup BinaryFiniteGL}
    (hU : IsOpenCompact U) {G : BergmanSpace k M.E} (hGU : ∀ w, G w ∈ fixedSubmodule M.σ U)
    (hGs : IsRotSmooth G)
    (hz : ∀ (θ : ℝ) (x : BinaryAdelicGL), realizeU M hU (realRep k M.E (rotGL θ) G) x = 0) :
    coeffMinus G 0 = 0 := by
  have hk2 : 2 ≤ k := by omega
  have hk3 : 3 ≤ k := by omega
  have : Fact (2 ≤ k) := ⟨hk2⟩
  have haU : coeffMinus G 0 ∈ fixedSubmodule M.σ U := coeffMinus_mem_fixed M hGU 0
  have hcU : ((-1 : ℂ) ^ k) • coeffMinus G 0 ∈ fixedSubmodule M.σ U :=
    Submodule.smul_mem _ _ haU
  have hεx : ∀ x, M.ε ⟨((-1 : ℂ) ^ k) • coeffMinus G 0, fixed_le_finiteSmooth M hU hcU⟩ x = 0 := by
    intro x
    obtain ⟨b, hb⟩ := exists_inner_secondRot M hU hk x
    let P : ℕ → ℂ := fun n => ((bergmanWeight k n : ℝ) : ℂ) * (-(((k : ℂ) + 2 * n) ^ 2)) *
      ⟪coeffPlus b n, coeffPlus G n⟫_ℂ
    let Q : ℕ → ℂ := fun n => ((bergmanWeight k n : ℝ) : ℂ) * (-(((k : ℂ) + 2 * n) ^ 2)) *
      ⟪coeffMinus b n, coeffMinus G n⟫_ℂ
    have hser : ∀ θ : ℝ, HasSum (fun n : ℕ => cexp ((((k : ℂ) + 2 * n) * θ) * I) * P n +
        cexp (-(((k : ℂ) + 2 * n) * θ) * I) * Q n)
        (realizeU M hU (realRep k M.E (rotGL θ) G) x) := by
      intro θ
      rw [hb _ (realRep_apply_mem M hGU _) (hGs.rot θ)]
      refine (hasSum_inner hk2 b (secondRot (realRep k M.E (rotGL θ) G))).congr_fun
        fun n => ?_
      rw [coeffPlus_secondRot hk2 (hGs.rot θ), coeffMinus_secondRot hk2 (hGs.rot θ),
        coeffPlus_realRep_rot, coeffMinus_realRep_rot]
      simp only [inner_smul_right, P, Q]
      ring
    have hVp : ∀ n, ‖coeffPlus (secondRot G) n‖ = ((k : ℝ) + 2 * n) ^ 2 * ‖coeffPlus G n‖ :=
      fun n => by rw [coeffPlus_secondRot hk2 hGs, norm_smul, norm_neg_sq]
    have hVm : ∀ n, ‖coeffMinus (secondRot G) n‖ = ((k : ℝ) + 2 * n) ^ 2 * ‖coeffMinus G n‖ :=
      fun n => by rw [coeffMinus_secondRot hk2 hGs, norm_smul, norm_neg_sq]
    have hPs : Summable fun n => ‖P n‖ := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
        (summable_weight_mul_plus hk2 b (secondRot G))
      simp only [P, norm_mul, Complex.norm_real, Real.norm_of_nonneg (bergmanWeight_pos hk2 n).le,
        norm_neg_sq, hVp]
      have h := norm_inner_le_norm (𝕜 := ℂ) (coeffPlus b n) (coeffPlus G n)
      have hw := (bergmanWeight_pos hk2 n).le
      have hm : 0 ≤ ((k : ℝ) + 2 * n) ^ 2 := by positivity
      calc bergmanWeight k n * ((k : ℝ) + 2 * n) ^ 2 * ‖⟪coeffPlus b n, coeffPlus G n⟫_ℂ‖
          ≤ bergmanWeight k n * ((k : ℝ) + 2 * n) ^ 2 * (‖coeffPlus b n‖ * ‖coeffPlus G n‖) :=
            mul_le_mul_of_nonneg_left h (mul_nonneg hw hm)
        _ = _ := by ring
    have hQs : Summable fun n => ‖Q n‖ := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
        (summable_weight_mul_minus hk2 b (secondRot G))
      simp only [Q, norm_mul, Complex.norm_real, Real.norm_of_nonneg (bergmanWeight_pos hk2 n).le,
        norm_neg_sq, hVm]
      have h := norm_inner_le_norm (𝕜 := ℂ) (coeffMinus b n) (coeffMinus G n)
      have hw := (bergmanWeight_pos hk2 n).le
      have hm : 0 ≤ ((k : ℝ) + 2 * n) ^ 2 := by positivity
      calc bergmanWeight k n * ((k : ℝ) + 2 * n) ^ 2 * ‖⟪coeffMinus b n, coeffMinus G n⟫_ℂ‖
          ≤ bergmanWeight k n * ((k : ℝ) + 2 * n) ^ 2 * (‖coeffMinus b n‖ * ‖coeffMinus G n‖) :=
            mul_le_mul_of_nonneg_left h (mul_nonneg hw hm)
        _ = _ := by ring
    have hQ0 : Q 0 = 0 := coeff_zero_of_tsum_eq_zero (k := k) (by omega) hPs hQs
      (fun θ => by rw [(hser θ).tsum_eq, hz θ x])
    have hLs := isRotSmooth_lowestMinus hk2 (((-1 : ℂ) ^ k) • coeffMinus G 0)
    have hL : realizeU M hU (lowestMinus hk2 (((-1 : ℂ) ^ k) • coeffMinus G 0)) x = Q 0 := by
      rw [hb _ (lowestMinus_mem_fixed M hk2 hcU) hLs,
        ← (hasSum_inner hk2 b _).tsum_eq, tsum_eq_single 0]
      · rw [coeffPlus_secondRot hk2 hLs, coeffMinus_secondRot hk2 hLs, coeffPlus_lowestMinus,
          coeffMinus_lowestMinus, ite_eq_left rfl, smul_zero, inner_zero_right, zero_add,
          inner_smul_right, inner_smul_right, inner_smul_right]
        have hneg : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
          rw [← mul_pow]
          norm_num
        simp only [Q]
        linear_combination (((bergmanWeight k 0 : ℝ) : ℂ) * (-(((k : ℂ) + 2 * ((0 : ℕ) : ℂ)) ^ 2)) *
          ⟪coeffMinus b 0, coeffMinus G 0⟫_ℂ) * hneg
      · intro n hn
        rw [coeffPlus_secondRot hk2 hLs, coeffMinus_secondRot hk2 hLs, coeffPlus_lowestMinus,
          coeffMinus_lowestMinus, ite_eq_right hn]
        simp
    have hrep := realizeU_lowestMinus M hk3 hU hcU x
    rw [hL, hQ0] at hrep
    exact (mul_eq_zero.mp hrep.symm).resolve_left (reproConst_ne_zero hk2)
  have hc0 : (⟨((-1 : ℂ) ^ k) • coeffMinus G 0, fixed_le_finiteSmooth M hU hcU⟩ :
      finiteSmooth M.σ) = 0 :=
    M.injective (by rw [map_zero]; funext x; exact hεx x)
  have hc : ((-1 : ℂ) ^ k) • coeffMinus G 0 = 0 := congrArg Subtype.val hc0
  exact (smul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (by norm_num))

/-- A smooth vector with zero realization is zero. -/
theorem eq_zero_of_realizeFun_eq_zero (hk : 6 ≤ k) (F : smoothSubmodule (bergmanRep M))
    (hF : realizeFun F = 0) : F = 0 := by
  have hU := level_isOpenCompact F
  have hFU : ∀ w, (F.val : BergmanSpace k M.E) w ∈ fixedSubmodule M.σ (level F) :=
    apply_mem_fixed (level_fixed F)
  have h1 : ∀ (r : GL (Fin 2) ℝ) (x : BinaryAdelicGL),
      realizeU M hU (realRep k M.E r F.val) x = 0 := by
    intro r x
    rw [realizeU_realRep M hU hFU, ← realizeFun_eq F hU hFU, hF, Pi.zero_apply]
  have hval : ∀ w : ℂ, w.im ≠ 0 → (F.val : BergmanSpace k M.E) w = 0 := by
    intro w hw
    have hG := coeffMinus_zero_eq_zero M hk hU (realRep_apply_mem M hFU (gBar w)⁻¹)
      (isRotSmooth_realRep_of_smooth F (gBar w)⁻¹) (fun θ x => by
        rw [realizeU_realRep M hU (realRep_apply_mem M hFU _)]
        exact h1 _ _)
    rw [coeffMinus, upperCoeff_zero_eq (BergmanSpace.differentiableOn_lowerPart _)] at hG
    have hI : (realRep k M.E (gBar w)⁻¹ F.val) (-I) = 0 :=
      (smul_eq_zero.mp hG).resolve_left (pow_ne_zero _ (mul_ne_zero two_ne_zero I_ne_zero))
    have hnegI : (-I).im ≠ 0 := by simp
    rw [realRep_apply _ _ hnegI, inv_inv, moeb_gBar_neg_I hw] at hI
    exact (smul_eq_zero.mp hI).resolve_left (autFactor_ne_zero k _ hnegI)
  apply Subtype.ext
  refine BergmanSpace.ext fun w => ?_
  by_cases hw : w.im = 0
  · rw [BergmanSpace.apply_eq_zero _ hw]
    rfl
  · exact hval w hw

end TernaryPeriodPolynomials.Regularity

end
