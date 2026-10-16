module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.WeakDeriv

@[expose] public section


/-!
# Mollification on `ℂ` and its interaction with weak derivatives

The mollifier `mol n` of radius `1/(n+1)`: smoothness, compact support, the formula
`∂_j (mol n v) = mol n (∂_j v)` for weak derivatives, and `P₁ ∂₁ + P₂ ∂₂` of a weak solution.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff Convolution

/-- The mollifier bump of radius `1/(n+1)`. -/
def bump (n : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]
    nlinarith⟩

/-- The normalised mollifier kernel of radius `1/(n+1)`. -/
def ker (n : ℕ) : ℂ → ℝ := (bump n).normed volume

theorem ker_nonneg (n : ℕ) (x : ℂ) : 0 ≤ ker n x := (bump n).nonneg_normed x

theorem integral_ker (n : ℕ) : ∫ x, ker n x = 1 := (bump n).integral_normed

theorem ker_contDiff (n : ℕ) : ContDiff ℝ ∞ (ker n) := (bump n).contDiff_normed

theorem ker_compact (n : ℕ) : HasCompactSupport (ker n) := (bump n).hasCompactSupport_normed

theorem ker_support (n : ℕ) : Function.support (ker n) = ball 0 (1 / ((n : ℝ) + 1)) :=
  (bump n).support_normed_eq

theorem ker_integrable (n : ℕ) : Integrable (ker n) := (bump n).integrable_normed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Mollification of a function on `ℂ`. -/
def mol (n : ℕ) (v : ℂ → X) : ℂ → X :=
  (ker n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v

theorem mol_apply (n : ℕ) (v : ℂ → X) (x : ℂ) : mol n v x = ∫ t, ker n t • v (x - t) := by
  simp [mol, convolution_def]

theorem mol_contDiff (n : ℕ) {v : ℂ → X} (hv : LocallyIntegrable v volume) :
    ContDiff ℝ ∞ (mol n v) :=
  (ker_compact n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (ker_contDiff n) hv

theorem mol_eq_zero (n : ℕ) {K : Set ℂ} {v : ℂ → X} (hv : ∀ᵐ z, z ∉ K → v z = 0) {x : ℂ}
    (hx : x ∉ cthickening (1 / ((n : ℝ) + 1)) K) : mol n v x = 0 := by
  rw [mol_apply]
  have hae : ∀ᵐ t : ℂ, x - t ∉ K → v (x - t) = 0 :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hv
  have : ∀ᵐ t : ℂ, ker n t • v (x - t) = 0 := by
    filter_upwards [hae] with t ht
    by_cases hk : ker n t = 0
    · simp [hk]
    · have : t ∈ ball (0 : ℂ) (1 / ((n : ℝ) + 1)) := by
        rw [← ker_support]; exact hk
      have hxt : x - t ∉ K := by
        intro hK
        apply hx
        apply mem_cthickening_of_dist_le x (x - t) _ K hK
        rw [dist_eq_norm]
        simpa using (mem_ball_zero_iff.mp this).le
      simp [ht hxt]
  rw [integral_congr_ae this]
  simp

theorem mol_hasCompactSupport (n : ℕ) {K : Set ℂ} (hK : IsCompact K) {v : ℂ → X}
    (hv : ∀ᵐ z, z ∉ K → v z = 0) : HasCompactSupport (mol n v) :=
  HasCompactSupport.intro (hK.cthickening (r := 1 / ((n : ℝ) + 1))) fun _ hx => mol_eq_zero n hv hx

theorem mol_fderiv_apply (n : ℕ) {v : ℂ → X} (hv : LocallyIntegrable v volume) (x e : ℂ) :
    fderiv ℝ (mol n v) x e = ∫ t, fderiv ℝ (ker n) t e • v (x - t) := by
  have h := (ker_compact n).hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((ker_contDiff n).of_le (by simp)) hv x
  have hint : Integrable fun t => (ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ (fderiv ℝ (ker n) t)
      (v (x - t)) := by
    have := (ker_compact n).fderiv (𝕜 := ℝ) |>.convolutionExists_left
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
      (((ker_contDiff n).continuous_fderiv (by simp))) hv x
    exact this
  rw [mol, h.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint e]
  rfl

/-- The reflected translate of the kernel, a test function. -/
theorem isTest_kerShift (n : ℕ) (x : ℂ) : IsTest fun y => ker n (x - y) :=
  ⟨(ker_contDiff n).comp (contDiff_const.sub contDiff_id),
    (ker_compact n).comp_homeomorph (Homeomorph.subLeft x)⟩

theorem fderiv_kerShift (n : ℕ) (x y e : ℂ) :
    fderiv ℝ (fun y => ker n (x - y)) y e = - fderiv ℝ (ker n) (x - y) e := by
  have h1 : HasFDerivAt (fun y => ker n (x - y))
      ((fderiv ℝ (ker n) (x - y)).comp (-(ContinuousLinearMap.id ℝ ℂ))) y :=
    ((ker_contDiff n).differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
  rw [h1.fderiv]
  simp

theorem mol_fderiv_eq (n : ℕ) {v : ℂ → X} (hv : LocallyIntegrable v volume) (x e : ℂ) :
    fderiv ℝ (mol n v) x e = - ∫ y, fderiv ℝ (fun y => ker n (x - y)) y e • v y := by
  rw [mol_fderiv_apply n hv x e]
  have e1 : ∫ t, fderiv ℝ (ker n) t e • v (x - t) = ∫ y, fderiv ℝ (ker n) (x - y) e • v y := by
    rw [← integral_sub_left_eq_self (fun t => fderiv ℝ (ker n) t e • v (x - t)) volume x]
    simp
  rw [e1, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [fderiv_kerShift, neg_smul, neg_neg]

theorem integral_kerShift_smul (n : ℕ) (g : ℂ → X) (x : ℂ) :
    ∫ y, ker n (x - y) • g y = mol n g x := by
  rw [mol_apply, ← integral_sub_left_eq_self (fun t => ker n t • g (x - t)) volume x]
  simp

theorem mol_wd (n : ℕ) {j : Fin 2} {v g : ℂ → X} (h : WD j v g) (hv : LocallyIntegrable v volume)
    (x : ℂ) : fderiv ℝ (mol n v) x (dir j) = mol n g x := by
  rw [mol_fderiv_eq n hv x (dir j), ← h _ (isTest_kerShift n x),
    integral_kerShift_smul]

/-- `P₁ ∂₁ v + P₂ ∂₂ v = f` in the weak sense. -/
def WeakEq (P : Fin 2 → X →L[ℝ] X) (v f : ℂ → X) : Prop :=
  ∀ φ : ℂ → ℝ, IsTest φ → ∑ j, P j (∫ z, fderiv ℝ φ z (dir j) • v z) = - ∫ z, φ z • f z

theorem mol_weakEq (n : ℕ) {P : Fin 2 → X →L[ℝ] X} {v f : ℂ → X} (h : WeakEq P v f)
    (hv : LocallyIntegrable v volume) (x : ℂ) :
    ∑ j, P j (fderiv ℝ (mol n v) x (dir j)) = mol n f x := by
  have := h _ (isTest_kerShift n x)
  rw [integral_kerShift_smul] at this
  rw [← neg_neg (mol n f x), ← this, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mol_fderiv_eq n hv x (dir j), map_neg]

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
