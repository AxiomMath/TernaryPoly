module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Continuous

@[expose] public section


/-!
# From `Hk` regularity to smooth representatives

Uniform convergence of the mollifiers, the weak `C¹` criterion `hasFDerivAt_of_weakDeriv`, and the
conclusion that a function in `Hk K (k + 2)` has a `C^k` representative.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section C1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem tendstoUniformly_mol {h : ℂ → X} (hc : Continuous h) (hs : HasCompactSupport h) :
    TendstoUniformly (fun n : ℕ => mol n h) h atTop := by
  have huc : UniformContinuous h := hs.uniformContinuous_of_continuous hc
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  filter_upwards [eventually_ge_atTop N] with n hn x
  have hr : (bump n).rOut < δ := by
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    exact lt_of_le_of_lt this hN
  have := ContDiffBump.dist_normed_convolution_le (φ := bump n) (μ := (volume : Measure ℂ))
    (g := h) (x₀ := x) (ε := ε / 2) hc.aestronglyMeasurable
    (fun y hy => (hδh (lt_trans (by simpa [dist_comm, Metric.mem_ball] using hy) hr)).le)
  rw [dist_comm]
  exact lt_of_le_of_lt this (half_lt_self hε)

/-- The candidate Fréchet derivative built from the two partial derivatives. -/
def derivCand (g0 g1 : ℂ → X) (z : ℂ) : ℂ →L[ℝ] X :=
  Complex.reCLM.smulRight (g0 z) + Complex.imCLM.smulRight (g1 z)

omit [CompleteSpace X] in
theorem derivCand_apply (g0 g1 : ℂ → X) (z e : ℂ) :
    derivCand g0 g1 z e = e.re • g0 z + e.im • g1 z := by
  simp [derivCand]

omit [CompleteSpace X] in
theorem norm_derivCand_le (a b : X) :
    ‖(Complex.reCLM.smulRight a + Complex.imCLM.smulRight b : ℂ →L[ℝ] X)‖ ≤ ‖a‖ + ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
  have h1 : ‖e.re • a‖ ≤ ‖e‖ * ‖a‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm e) (norm_nonneg _)
  have h2 : ‖e.im • b‖ ≤ ‖e‖ * ‖b‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm e) (norm_nonneg _)
  calc ‖(Complex.reCLM.smulRight a + Complex.imCLM.smulRight b : ℂ →L[ℝ] X) e‖
      = ‖e.re • a + e.im • b‖ := by simp
    _ ≤ ‖e.re • a‖ + ‖e.im • b‖ := norm_add_le _ _
    _ ≤ ‖e‖ * ‖a‖ + ‖e‖ * ‖b‖ := add_le_add h1 h2
    _ = (‖a‖ + ‖b‖) * ‖e‖ := by ring

omit [CompleteSpace X] in
theorem fderiv_mol_eq_derivCand (n : ℕ) {w g0 g1 : ℂ → X} (hwl : LocallyIntegrable w volume)
    (hW0 : WD 0 w g0) (hW1 : WD 1 w g1) (x : ℂ) :
    fderiv ℝ (mol n w) x = derivCand (mol n g0) (mol n g1) x := by
  ext e
  have hlin : fderiv ℝ (mol n w) x e =
      e.re • fderiv ℝ (mol n w) x 1 + e.im • fderiv ℝ (mol n w) x Complex.I := by
    conv_lhs => rw [show e = e.re • (1 : ℂ) + e.im • Complex.I by
      apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul]
  rw [hlin, derivCand_apply]
  have h0 : fderiv ℝ (mol n w) x 1 = mol n g0 x := by
    simpa [dir] using mol_wd n hW0 hwl x
  have h1 : fderiv ℝ (mol n w) x Complex.I = mol n g1 x := by
    simpa [dir] using mol_wd n hW1 hwl x
  rw [h0, h1]

theorem hasFDerivAt_of_weakDeriv {w g0 g1 : ℂ → X} (hw : Continuous w) (hwc : HasCompactSupport w)
    (h0 : Continuous g0) (hc0 : HasCompactSupport g0) (h1 : Continuous g1)
    (hc1 : HasCompactSupport g1) (hW0 : WD 0 w g0) (hW1 : WD 1 w g1) (z : ℂ) :
    HasFDerivAt w (derivCand g0 g1 z) z := by
  have hwl : LocallyIntegrable w volume := hw.locallyIntegrable
  have u0 := tendstoUniformly_mol h0 hc0
  have u1 := tendstoUniformly_mol h1 hc1
  have uw := tendstoUniformly_mol hw hwc
  have hf' : TendstoUniformly (fun n x => derivCand (mol n g0) (mol n g1) x)
      (derivCand g0 g1) atTop := by
    rw [Metric.tendstoUniformly_iff] at u0 u1 ⊢
    intro ε hε
    filter_upwards [u0 (ε / 2) (half_pos hε), u1 (ε / 2) (half_pos hε)] with n hn0 hn1 x
    have e : derivCand g0 g1 x - derivCand (mol n g0) (mol n g1) x =
        Complex.reCLM.smulRight (g0 x - mol n g0 x) + Complex.imCLM.smulRight (g1 x - mol n g1 x) := by
      ext e
      simp [derivCand, smul_sub]
      abel
    rw [dist_eq_norm, e]
    calc _ ≤ ‖g0 x - mol n g0 x‖ + ‖g1 x - mol n g1 x‖ := norm_derivCand_le _ _
      _ < ε / 2 + ε / 2 := by
          have a := hn0 x
          have b := hn1 x
          rw [dist_eq_norm] at a b
          linarith
      _ = ε := add_halves ε
  refine hasFDerivAt_of_tendstoUniformly (f := fun n => mol n w)
    (f' := fun n x => derivCand (mol n g0) (mol n g1) x) hf'
    (fun n x => ?_) (fun x => uw.tendsto_at x) z
  have hd := ((mol_contDiff n hwl).differentiable (by simp) x).hasFDerivAt
  rwa [fderiv_mol_eq_derivCand n hwl hW0 hW1 x] at hd

end C1

section Smooth

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem Hk.mono_le {K : Set ℂ} {k m : ℕ} (h : k ≤ m) {v : ℂ → X} (hv : Hk K m v) : Hk K k v := by
  induction m, h using Nat.le_induction with
  | base => exact hv
  | succ m _ ih => exact ih hv.mono

theorem exists_contDiff_of_Hk {K : Set ℂ} (hK : IsCompact K) :
    ∀ (k : ℕ) {v : ℂ → X}, Hk K (k + 2) v → ∃ w : ℂ → X, ContDiff ℝ k w ∧ v =ᵐ[volume] w ∧
      ∀ z, z ∉ cthickening 1 K → w z = 0 := by
  intro k
  induction k with
  | zero =>
    intro v hv
    obtain ⟨w, hwc, hvw, hwz⟩ := exists_continuous_of_Hk_two hK hv
    exact ⟨w, by simpa using hwc, hvw, hwz⟩
  | succ k ih =>
    intro v hv
    have hv3 : Hk K ((k + 2) + 1) v := hv
    obtain ⟨w, hwc, hvw, hwz⟩ := exists_continuous_of_Hk_two hK (hv.mono_le (by omega))
    obtain ⟨hl, g, hg, hgk⟩ := hv3
    have hK₁ : IsCompact (cthickening 1 K) := hK.cthickening
    have hex : ∀ j, ∃ ĝ : ℂ → X, ContDiff ℝ k ĝ ∧ g j =ᵐ[volume] ĝ ∧
        ∀ z, z ∉ cthickening 1 K → ĝ z = 0 := fun j => ih (hgk j)
    choose ĝ hĝd hĝe hĝz using hex
    have hW : ∀ j, WD j w (ĝ j) := fun j => ((hg j).congr_left hvw).congr_right (hĝe j)
    have hcs : ∀ j, HasCompactSupport (ĝ j) := fun j => HasCompactSupport.intro hK₁ (hĝz j)
    have hD : ∀ z, HasFDerivAt w (derivCand (ĝ 0) (ĝ 1) z) z := fun z =>
      hasFDerivAt_of_weakDeriv hwc (HasCompactSupport.intro hK₁ hwz) (hĝd 0).continuous (hcs 0)
        (hĝd 1).continuous (hcs 1) (hW 0) (hW 1) z
    refine ⟨w, ?_, hvw, hwz⟩
    have hfd : fderiv ℝ w = derivCand (ĝ 0) (ĝ 1) := funext fun z => (hD z).fderiv
    have hdc : ContDiff ℝ k (derivCand (ĝ 0) (ĝ 1)) := by
      have e : derivCand (ĝ 0) (ĝ 1) = fun z =>
          (ContinuousLinearMap.smulRightL ℝ ℂ X Complex.reCLM) (ĝ 0 z) +
            (ContinuousLinearMap.smulRightL ℝ ℂ X Complex.imCLM) (ĝ 1 z) := by
        funext z
        rfl
      rw [e]
      exact ((ContinuousLinearMap.smulRightL ℝ ℂ X Complex.reCLM).contDiff.comp (hĝd 0)).add
        ((ContinuousLinearMap.smulRightL ℝ ℂ X Complex.imCLM).contDiff.comp (hĝd 1))
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by norm_cast]
    rw [contDiff_succ_iff_fderiv]
    exact ⟨fun z => (hD z).differentiableAt, fun h => by simp at h, hfd ▸ hdc⟩

end Smooth

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
