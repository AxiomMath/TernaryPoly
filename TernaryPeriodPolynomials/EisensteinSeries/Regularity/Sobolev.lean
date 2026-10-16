module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Rotation
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.L1
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.SobolevSeq

@[expose] public section


/-!
# Weighted `L¹` bounds for vectors with two rotation derivatives

The weighted `L¹` integral `∫ ‖F w‖ |Im w|^(k/2) dμ_hyp` of a Bergman vector is at most
`2^(2-k) Σ γ_n (‖a⁺_n‖ + ‖a⁻_n‖)`, `γ_n = ∫_D |ζ|^n (1 - |ζ|²)^(k/2-2)`, in terms of its
coefficients (`l1Integral_le_tsum`). The rotation `rotGL θ` multiplies `a^±_n` by
`e^(±i(k+2n)θ)`, so a second rotation derivative `V` has coefficients `-(k+2n)² a^±_n`; for
`k ≥ 6` the moments satisfy `Σ γ_n²/((k+2n)⁴ β_n) < ∞` and Cauchy–Schwarz gives
`l1Integral F ≤ sobolevConst k · ‖V‖` (`l1Integral_le_of_second`). Smooth vectors of the
holomorphic model have smooth rotation orbits, hence finite weighted `L¹` integrals.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors

namespace TernaryPeriodPolynomials.Regularity

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The weighted `L¹` integral in terms of the coefficients. -/
theorem l1Integral_le_tsum (hk : 3 ≤ k) (F : BergmanSpace k E) :
    l1Integral F ≤ ∑' n, ENNReal.ofReal ((2 : ℝ) ^ (2 - (k : ℝ)) *
      discMoment n ((k : ℝ) / 2 - 2) * (‖coeffPlus F n‖ + ‖coeffMinus F n‖)) := by
  rw [l1Integral, lintegral_hypMeasure_split]
  have h1 : ∫⁻ z in upper, ENNReal.ofReal (‖F z‖ * |z.im| ^ ((k : ℝ) / 2)) ∂hypMeasure =
      ∫⁻ z in upper, ENNReal.ofReal (‖(F : ℂ → E) z‖ * z.im ^ ((k : ℝ) / 2)) ∂hypMeasure :=
    setLIntegral_congr_fun measurableSet_upper fun z hz => by
      rw [abs_of_pos (mem_upper_iff.1 hz)]
  have h2 : ∫⁻ z in upper, ENNReal.ofReal (‖F (-z)‖ * |(-z).im| ^ ((k : ℝ) / 2)) ∂hypMeasure =
      ∫⁻ z in upper, ENNReal.ofReal (‖lowerPart (F : ℂ → E) z‖ * z.im ^ ((k : ℝ) / 2))
        ∂hypMeasure :=
    setLIntegral_congr_fun measurableSet_upper fun z hz => by
      rw [Complex.neg_im, abs_neg, abs_of_pos (mem_upper_iff.1 hz)]
      rfl
  rw [h1, h2]
  refine (add_le_add (lintegral_upper_norm_le hk (BergmanSpace.differentiableOn_upper F))
    (lintegral_upper_norm_le hk (BergmanSpace.differentiableOn_lowerPart F))).trans ?_
  rw [← ENNReal.tsum_add]
  refine le_of_eq (tsum_congr fun n => ?_)
  have hγ := discMoment_nonneg n ((k : ℝ) / 2 - 2)
  rw [← ENNReal.ofReal_add (mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) hγ))
    (mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) hγ))]
  congr 1
  unfold coeffPlus coeffMinus
  ring

/-- The constant of the second-derivative bound. -/
def sobolevConst (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 - (k : ℝ)) *
    Real.sqrt (∑' n : ℕ, discMoment n ((k : ℝ) / 2 - 2) ^ 2 /
      ((((k : ℝ) + 2 * n) ^ 2) ^ 2 * bergmanWeight k n)) * Real.sqrt 2

theorem sobolevConst_nonneg (k : ℕ) : 0 ≤ sobolevConst k := by
  unfold sobolevConst
  positivity

omit [CompleteSpace E] in
theorem norm_neg_sq_smul (n : ℕ) (e : E) :
    ‖-(((k : ℂ) + 2 * n) ^ 2) • e‖ = ((k : ℝ) + 2 * n) ^ 2 * ‖e‖ := by
  have hc : ((k : ℂ) + 2 * n) = (((k : ℝ) + 2 * n : ℝ) : ℂ) := by push_cast; ring
  rw [norm_smul, norm_neg, norm_pow, hc, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- **Sobolev-type bound.** If `V` has the coefficients of a second rotation derivative of `F`,
then the weighted `L¹` integral of `F` is at most `sobolevConst k · ‖V‖`. -/
theorem l1Integral_le_of_second (hk : 6 ≤ k) {F V : BergmanSpace k E}
    (hplus : ∀ n, coeffPlus V n = -(((k : ℂ) + 2 * n) ^ 2) • coeffPlus F n)
    (hminus : ∀ n, coeffMinus V n = -(((k : ℂ) + 2 * n) ^ 2) • coeffMinus F n) :
    l1Integral F ≤ ENNReal.ofReal (sobolevConst k * ‖V‖) := by
  have hk2 : 2 ≤ k := by omega
  have hk3 : 3 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hm : ∀ n : ℕ, 0 < ((k : ℝ) + 2 * n) ^ 2 := fun n => by positivity
  have hV : HasSum (fun n => bergmanWeight k n *
      ((((k : ℝ) + 2 * n) ^ 2 * ‖coeffPlus F n‖) ^ 2 +
        (((k : ℝ) + 2 * n) ^ 2 * ‖coeffMinus F n‖) ^ 2)) (‖V‖ ^ 2) := by
    refine (hasSum_norm_sq hk2 V).congr_fun fun n => ?_
    rw [hplus, hminus, norm_neg_sq_smul, norm_neg_sq_smul]
    unfold bergmanWeight
    ring
  have h4 : (4 : ℝ) ^ (1 - (k : ℝ)) = ((4 : ℝ) ^ ((k : ℝ) - 1))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), neg_sub]
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ ((k : ℝ) - 1) := by positivity
  have hS : Summable fun n : ℕ => discMoment n ((k : ℝ) / 2 - 2) ^ 2 /
      ((((k : ℝ) + 2 * n) ^ 2) ^ 2 * bergmanWeight k n) := by
    refine ((summable_moment_ratio k hk).mul_left ((4 : ℝ) ^ ((k : ℝ) - 1))).congr fun n => ?_
    have hβ := (BergmanAux.discMoment_pos_k hk2 n).ne'
    have hmn := (hm n).ne'
    have h4ne := h4pos.ne'
    unfold bergmanWeight
    rw [h4]
    field_simp
  obtain ⟨hsum, hle⟩ := sobolev_seq (β := bergmanWeight k)
    (γ := fun n => discMoment n ((k : ℝ) / 2 - 2)) (m := fun n => ((k : ℝ) + 2 * n) ^ 2)
    (a := fun n => ‖coeffPlus F n‖) (b := fun n => ‖coeffMinus F n‖)
    (bergmanWeight_pos hk2) (fun n => discMoment_nonneg _ _) hm (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hS hV
  have hnn : ∀ n, 0 ≤ (2 : ℝ) ^ (2 - (k : ℝ)) *
      (discMoment n ((k : ℝ) / 2 - 2) * (‖coeffPlus F n‖ + ‖coeffMinus F n‖)) := fun n =>
    mul_nonneg (by positivity) (mul_nonneg (discMoment_nonneg _ _) (by positivity))
  calc l1Integral F ≤ ∑' n, ENNReal.ofReal ((2 : ℝ) ^ (2 - (k : ℝ)) *
        discMoment n ((k : ℝ) / 2 - 2) * (‖coeffPlus F n‖ + ‖coeffMinus F n‖)) :=
        l1Integral_le_tsum hk3 F
    _ = ENNReal.ofReal (∑' n, (2 : ℝ) ^ (2 - (k : ℝ)) *
        (discMoment n ((k : ℝ) / 2 - 2) * (‖coeffPlus F n‖ + ‖coeffMinus F n‖))) := by
        rw [ENNReal.ofReal_tsum_of_nonneg hnn (hsum.mul_left _)]
        simp only [mul_assoc]
    _ ≤ ENNReal.ofReal (sobolevConst k * ‖V‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left]
        refine (mul_le_mul_of_nonneg_left hle (by positivity)).trans (le_of_eq ?_)
        unfold sobolevConst
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (norm_nonneg V)]
        ring

/-! ### Second rotation derivatives -/

/-- The second derivative of the rotation orbit `θ ↦ rotGL θ · F` at `θ = 0`. -/
def secondRot (F : BergmanSpace k E) : BergmanSpace k E :=
  deriv (deriv fun θ : ℝ => realRep k E (rotGL θ) F) 0

/-- The rotation orbit of `F` is smooth. -/
def IsRotSmooth (F : BergmanSpace k E) : Prop :=
  ContDiff ℝ ∞ fun θ : ℝ => realRep k E (rotGL θ) F

omit [CompleteSpace E] in
theorem IsRotSmooth.hasDerivAt {F : BergmanSpace k E} (hF : IsRotSmooth F) (θ : ℝ) :
    HasDerivAt (fun t => realRep k E (rotGL t) F)
      (deriv (fun t => realRep k E (rotGL t) F) θ) θ :=
  ((hF.differentiable (by simp)).differentiableAt).hasDerivAt

omit [CompleteSpace E] in
theorem IsRotSmooth.hasDerivAt_deriv {F : BergmanSpace k E} (hF : IsRotSmooth F) :
    HasDerivAt (deriv fun t => realRep k E (rotGL t) F) (secondRot F) 0 := by
  have h := hF.iterate_deriv 1
  simp only [Function.iterate_one] at h
  exact ((h.differentiable (by simp)).differentiableAt).hasDerivAt

theorem coeffPlus_secondRot (hk : 2 ≤ k) {F : BergmanSpace k E} (hF : IsRotSmooth F) (n : ℕ) :
    coeffPlus (secondRot F) n = -(((k : ℂ) + 2 * n) ^ 2) • coeffPlus F n :=
  coeffPlus_of_hasDerivAt_rot hk hF.hasDerivAt hF.hasDerivAt_deriv n

theorem coeffMinus_secondRot (hk : 2 ≤ k) {F : BergmanSpace k E} (hF : IsRotSmooth F) (n : ℕ) :
    coeffMinus (secondRot F) n = -(((k : ℂ) + 2 * n) ^ 2) • coeffMinus F n :=
  coeffMinus_of_hasDerivAt_rot hk hF.hasDerivAt hF.hasDerivAt_deriv n

theorem l1Integral_le_secondRot (hk : 6 ≤ k) {F : BergmanSpace k E} (hF : IsRotSmooth F) :
    l1Integral F ≤ ENNReal.ofReal (sobolevConst k * ‖secondRot F‖) :=
  l1Integral_le_of_second hk (coeffPlus_secondRot (by omega) hF)
    (coeffMinus_secondRot (by omega) hF)

theorem L1Finite.of_isRotSmooth (hk : 6 ≤ k) {F : BergmanSpace k E} (hF : IsRotSmooth F) :
    L1Finite F :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (l1Integral_le_secondRot hk hF)

omit [CompleteSpace E] in
theorem IsRotSmooth.add {F G : BergmanSpace k E} (hF : IsRotSmooth F) (hG : IsRotSmooth G) :
    IsRotSmooth (F + G) := by
  unfold IsRotSmooth at *
  simpa only [map_add] using hF.add hG

omit [CompleteSpace E] in
theorem IsRotSmooth.smul (c : ℂ) {F : BergmanSpace k E} (hF : IsRotSmooth F) :
    IsRotSmooth (c • F) := by
  unfold IsRotSmooth at *
  simpa only [map_smul] using hF.const_smul c

omit [CompleteSpace E] in
theorem isRotSmooth_zero : IsRotSmooth (0 : BergmanSpace k E) := by
  unfold IsRotSmooth
  simpa only [map_zero] using (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => (0 : BergmanSpace k E))

variable (k E) in
/-- The vectors with smooth rotation orbits. -/
def rotSmoothSubmodule : Submodule ℂ (BergmanSpace k E) where
  carrier := {F | IsRotSmooth F}
  add_mem' := IsRotSmooth.add
  zero_mem' := isRotSmooth_zero
  smul_mem' c _ hF := IsRotSmooth.smul c hF

omit [CompleteSpace E] in
theorem secondRot_add {F G : BergmanSpace k E} (hF : IsRotSmooth F) (hG : IsRotSmooth G) :
    secondRot (F + G) = secondRot F + secondRot G := by
  have hd : deriv (fun θ : ℝ => realRep k E (rotGL θ) (F + G)) = fun θ =>
      deriv (fun t => realRep k E (rotGL t) F) θ + deriv (fun t => realRep k E (rotGL t) G) θ := by
    funext θ
    have hfun : (fun θ : ℝ => realRep k E (rotGL θ) (F + G)) =
        fun θ => realRep k E (rotGL θ) F + realRep k E (rotGL θ) G :=
      funext fun θ => map_add _ _ _
    rw [hfun]
    exact ((hF.hasDerivAt θ).add (hG.hasDerivAt θ)).deriv
  unfold secondRot
  rw [hd]
  exact (hF.hasDerivAt_deriv.add hG.hasDerivAt_deriv).deriv

omit [CompleteSpace E] in
theorem secondRot_smul (c : ℂ) {F : BergmanSpace k E} (hF : IsRotSmooth F) :
    secondRot (c • F) = c • secondRot F := by
  have hd : deriv (fun θ : ℝ => realRep k E (rotGL θ) (c • F)) = fun θ =>
      c • deriv (fun t => realRep k E (rotGL t) F) θ := by
    funext θ
    have hfun : (fun θ : ℝ => realRep k E (rotGL θ) (c • F)) =
        fun θ => c • realRep k E (rotGL θ) F :=
      funext fun θ => map_smul _ _ _
    rw [hfun]
    exact ((hF.hasDerivAt θ).const_smul c).deriv
  unfold secondRot
  rw [hd]
  exact (hF.hasDerivAt_deriv.const_smul c).deriv

variable (k E) in
/-- The second rotation derivative as a linear map on vectors with smooth rotation orbits. -/
def secondRotL : rotSmoothSubmodule k E →ₗ[ℂ] BergmanSpace k E where
  toFun F := secondRot (F : BergmanSpace k E)
  map_add' F G := secondRot_add F.2 G.2
  map_smul' c F := secondRot_smul c F.2

/-! ### Smooth vectors of the holomorphic model -/

theorem invertibleMatrix_val (g : GL (Fin 2) ℝ) : invertibleMatrix g.val = g := by
  unfold invertibleMatrix
  rw [dite_eq_left (gl_det_ne_zero g)]
  exact Units.ext (Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _)

theorem contDiff_rotGL_val : ContDiff ℝ ⊤ fun θ : ℝ => (rotGL θ).val := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa only [Fin.zero_eta, Fin.isValue, rotGL_00] using Real.contDiff_cos
  · simpa only [Fin.zero_eta, Fin.mk_one, Fin.isValue, rotGL_01] using Real.contDiff_sin.neg
  · simpa only [Fin.zero_eta, Fin.mk_one, Fin.isValue, rotGL_10] using Real.contDiff_sin
  · simpa only [Fin.mk_one, Fin.isValue, rotGL_11] using Real.contDiff_cos

variable {M : FiniteModel k}

/-- The rotation orbit of a smooth vector is real analytic. -/
theorem contDiff_rot_of_smooth (F : smoothSubmodule (bergmanRep M)) :
    ContDiff ℝ ⊤ fun θ : ℝ => realRep k M.E (rotGL θ) F.val := by
  have hs := (mem_smoothSubmodule.mp F.property).1
  have hρ : ContDiff ℝ ⊤ fun θ : ℝ => (fun _ : Fin 1 => (rotGL θ).val) :=
    contDiff_pi.mpr fun _ => contDiff_rotGL_val
  have hcomp := hs.comp_contDiff hρ fun θ i => gl_det_ne_zero (rotGL θ)
  have hfun : (fun θ : ℝ => realRep k M.E (rotGL θ) F.val) =
      (fun A : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        bergmanRep M (atInfinity ((fun i => invertibleMatrix (A i)) 0)) F.val) ∘
        (fun θ : ℝ => fun _ : Fin 1 => (rotGL θ).val) := by
    funext θ
    simp only [Function.comp, invertibleMatrix_val, bergmanRep_atInfinity]
  rw [hfun]
  exact hcomp

theorem isRotSmooth_of_smooth (F : smoothSubmodule (bergmanRep M)) : IsRotSmooth F.val :=
  (contDiff_rot_of_smooth F).of_le le_top

theorem isRotSmooth_realRep_of_smooth (F : smoothSubmodule (bergmanRep M))
    (r : GL (Fin 2) ℝ) : IsRotSmooth (realRep k M.E r F.val) := by
  have h := isRotSmooth_of_smooth (M := M)
    ⟨bergmanRep M (atInfinity r) F.val, smooth_stable (bergmanRep_unitary M) _ F.property⟩
  change IsRotSmooth (bergmanRep M (atInfinity r) F.val) at h
  rwa [bergmanRep_atInfinity] at h

theorem l1Finite_of_smooth (hk : 6 ≤ k) (F : smoothSubmodule (bergmanRep M)) :
    L1Finite F.val :=
  L1Finite.of_isRotSmooth hk (isRotSmooth_of_smooth F)

end TernaryPeriodPolynomials.Regularity

end
