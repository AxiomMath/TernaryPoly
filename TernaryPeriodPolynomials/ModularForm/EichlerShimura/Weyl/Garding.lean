module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.MollifyL2
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

@[expose] public section


/-!
# Gårding's identity for Dirac-type operators in two variables

For symmetric, involutive, anticommuting `P₀, P₁` (the principal symbols), smooth compactly supported
`φ : ℂ → X` satisfy `‖∂₀ φ‖₂² + ‖∂₁ φ‖₂² = ‖P₀ ∂₀ φ + P₁ ∂₁ φ‖₂²`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem contDiff_fderiv_apply {f : ℂ → X} (hf : ContDiff ℝ ∞ f) (e : ℂ) :
    ContDiff ℝ ∞ fun z => fderiv ℝ f z e :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_fderiv_apply {f : ℂ → X} (hf : HasCompactSupport f) (e : ℂ) :
    HasCompactSupport fun z => fderiv ℝ f z e :=
  (hf.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] X => L e) (by simp)

theorem hasCompactSupport_inner_right {a b : ℂ → X} (hb : HasCompactSupport b) :
    HasCompactSupport fun z => ⟪a z, b z⟫_ℝ :=
  hb.mono' fun z hz => subset_tsupport b fun h0 => hz (by simp [h0])

theorem hasCompactSupport_inner_left {a b : ℂ → X} (ha : HasCompactSupport a) :
    HasCompactSupport fun z => ⟪a z, b z⟫_ℝ :=
  ha.mono' fun z hz => subset_tsupport a fun h0 => hz (by simp [h0])

/-- Integration by parts for `X`-valued smooth compactly supported functions. -/
theorem ibp_inner [CompleteSpace X] {f g : ℂ → X} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (v : ℂ) :
    ∫ z, ⟪f z, fderiv ℝ g z v⟫_ℝ = - ∫ z, ⟪fderiv ℝ f z v, g z⟫_ℝ := by
  have hdf := contDiff_fderiv_apply hf v
  have hdg := contDiff_fderiv_apply hg v
  have c1 : Integrable fun z => ⟪fderiv ℝ f z v, g z⟫_ℝ :=
    (Continuous.inner (𝕜 := ℝ) hdf.continuous hg.continuous).integrable_of_hasCompactSupport (hasCompactSupport_inner_right hcg)
  have c2 : Integrable fun z => ⟪f z, fderiv ℝ g z v⟫_ℝ :=
    (Continuous.inner (𝕜 := ℝ) hf.continuous hdg.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_inner_left hcf)
  have c3 : Integrable fun z => ⟪f z, g z⟫_ℝ :=
    (Continuous.inner (𝕜 := ℝ) hf.continuous hg.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_inner_left hcf)
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innerSL ℝ) (μ := volume)
    (v := v) c1 c2 c3 (fun x _ => (hf.differentiable (by simp)) x)
    (fun x _ => (hg.differentiable (by simp)) x)

/-- A pair of symmetric involutions that anticommute: the principal symbols of a Dirac-type
first order operator in two variables. -/
structure DiracPair (P : Fin 2 → X →L[ℝ] X) : Prop where
  selfAdj : ∀ j x y, ⟪P j x, y⟫_ℝ = ⟪x, P j y⟫_ℝ
  sq : ∀ j x, P j (P j x) = x
  anti : ∀ x, P 0 (P 1 x) = - P 1 (P 0 x)

namespace DiracPair

variable {P : Fin 2 → X →L[ℝ] X} (hP : DiracPair P)
include hP

theorem norm_apply (j : Fin 2) (x : X) : ‖P j x‖ = ‖x‖ := by
  have : ‖P j x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hP.selfAdj, hP.sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

theorem inner_anti (a b : X) : ⟪b, P 0 (P 1 a)⟫_ℝ = - ⟪a, P 0 (P 1 b)⟫_ℝ := by
  calc ⟪b, P 0 (P 1 a)⟫_ℝ = ⟪P 0 b, P 1 a⟫_ℝ := (hP.selfAdj 0 b _).symm
    _ = ⟪P 1 (P 0 b), a⟫_ℝ := (hP.selfAdj 1 (P 0 b) a).symm
    _ = - ⟪P 0 (P 1 b), a⟫_ℝ := by
        rw [hP.anti b, inner_neg_left, neg_neg]
    _ = - ⟪a, P 0 (P 1 b)⟫_ℝ := by rw [real_inner_comm]

end DiracPair

theorem fderiv_symm {φ : ℂ → X} (hφ : ContDiff ℝ ∞ φ) (z e₀ e₁ : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ φ z e₁) z e₀ = fderiv ℝ (fun z => fderiv ℝ φ z e₀) z e₁ := by
  have h : ∀ e, fderiv ℝ (fun z => fderiv ℝ φ z e) z = (fderiv ℝ (fderiv ℝ φ) z).flip e := by
    intro e
    have hc : DifferentiableAt ℝ (fderiv ℝ φ) z :=
      (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
    rw [fderiv_clm_apply hc (differentiableAt_const e)]
    simp
  rw [h, h]
  have hca : ContDiffAt ℝ ∞ φ z := hφ.contDiffAt
  have := ContDiffAt.isSymmSndFDerivAt hca (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [ContinuousLinearMap.flip_apply]
  exact this e₀ e₁

/-- The product of the two symbols. -/
def Tm (P : Fin 2 → X →L[ℝ] X) : X →L[ℝ] X := (P 0).comp (P 1)

theorem Tm_apply (P : Fin 2 → X →L[ℝ] X) (x : X) : Tm P x = P 0 (P 1 x) := rfl

theorem fderiv_Tm {P : Fin 2 → X →L[ℝ] X} {d : ℂ → X} (hd : ContDiff ℝ ∞ d) (z e : ℂ) :
    fderiv ℝ (fun z => Tm P (d z)) z e = Tm P (fderiv ℝ d z e) := by
  have := (Tm P).hasFDerivAt.comp z ((hd.differentiable (by simp)) z).hasFDerivAt
  have h : (fun z => Tm P (d z)) = ⇑(Tm P) ∘ d := rfl
  rw [h, this.fderiv]
  rfl

theorem real_aux (A J : ℝ) (h1 : -A = -J) (h2 : J = -A) : A = 0 := by linarith

theorem cross_integral [CompleteSpace X] {P : Fin 2 → X →L[ℝ] X} (hP : DiracPair P) {φ : ℂ → X}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, ⟪fderiv ℝ φ z (dir 0), Tm P (fderiv ℝ φ z (dir 1))⟫_ℝ = 0 := by
  have cd0 := contDiff_fderiv_apply hφ (dir 0)
  have cd1 := contDiff_fderiv_apply hφ (dir 1)
  have kd0 := hasCompactSupport_fderiv_apply hc (dir 0)
  have kd1 := hasCompactSupport_fderiv_apply hc (dir 1)
  have hA' : ∫ z, ⟪φ z, Tm P (fderiv ℝ (fun z => fderiv ℝ φ z (dir 1)) z (dir 0))⟫_ℝ =
      -∫ z, ⟪fderiv ℝ φ z (dir 0), Tm P (fderiv ℝ φ z (dir 1))⟫_ℝ := by
    have h := ibp_inner hφ ((Tm P).contDiff.comp cd1) hc (kd1.comp_left (g := Tm P) (map_zero _))
      (dir 0)
    have e : (fun z => ⟪φ z, fderiv ℝ (fun z => Tm P (fderiv ℝ φ z (dir 1))) z (dir 0)⟫_ℝ) =
        fun z => ⟪φ z, Tm P (fderiv ℝ (fun z => fderiv ℝ φ z (dir 1)) z (dir 0))⟫_ℝ :=
      funext fun z => by rw [fderiv_Tm cd1]
    exact (congrArg (fun f => ∫ z, f z) e.symm).trans h
  have hB' : ∫ z, ⟪φ z, Tm P (fderiv ℝ (fun z => fderiv ℝ φ z (dir 0)) z (dir 1))⟫_ℝ =
      -∫ z, ⟪fderiv ℝ φ z (dir 1), Tm P (fderiv ℝ φ z (dir 0))⟫_ℝ := by
    have h := ibp_inner hφ ((Tm P).contDiff.comp cd0) hc (kd0.comp_left (g := Tm P) (map_zero _))
      (dir 1)
    have e : (fun z => ⟪φ z, fderiv ℝ (fun z => Tm P (fderiv ℝ φ z (dir 0))) z (dir 1)⟫_ℝ) =
        fun z => ⟪φ z, Tm P (fderiv ℝ (fun z => fderiv ℝ φ z (dir 0)) z (dir 1))⟫_ℝ :=
      funext fun z => by rw [fderiv_Tm cd0]
    exact (congrArg (fun f => ∫ z, f z) e.symm).trans h
  have hC : (fun z => ⟪φ z, Tm P (fderiv ℝ (fun z => fderiv ℝ φ z (dir 1)) z (dir 0))⟫_ℝ) =
      fun z => ⟪φ z, Tm P (fderiv ℝ (fun z => fderiv ℝ φ z (dir 0)) z (dir 1))⟫_ℝ :=
    funext fun z => by rw [fderiv_symm hφ z (dir 0) (dir 1)]
  have e3 : ∫ z, ⟪fderiv ℝ φ z (dir 1), Tm P (fderiv ℝ φ z (dir 0))⟫_ℝ =
      - ∫ z, ⟪fderiv ℝ φ z (dir 0), Tm P (fderiv ℝ φ z (dir 1))⟫_ℝ := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun z => hP.inner_anti _ _)
  refine real_aux _ _ ?_ e3
  rw [← hA', ← hB', hC]

theorem norm_sum_sq {P : Fin 2 → X →L[ℝ] X} (hP : DiracPair P) (a b : X) :
    ‖P 0 a + P 1 b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * ⟪a, Tm P b⟫_ℝ := by
  rw [norm_add_sq_real, hP.norm_apply, hP.norm_apply, hP.selfAdj, Tm_apply]
  ring

theorem integrable_norm_sq_fderiv {φ : ℂ → X} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (e : ℂ) : Integrable fun z => ‖fderiv ℝ φ z e‖ ^ 2 :=
  ((contDiff_fderiv_apply hφ e).continuous.norm.pow 2).integrable_of_hasCompactSupport
    ((hasCompactSupport_fderiv_apply hc e).mono' fun z hz =>
      subset_tsupport (fun z => fderiv ℝ φ z e) fun h0 => hz (by simp [h0]))

theorem integrable_cross {P : Fin 2 → X →L[ℝ] X} {φ : ℂ → X}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable fun z => ⟪fderiv ℝ φ z (dir 0), Tm P (fderiv ℝ φ z (dir 1))⟫_ℝ :=
  (Continuous.inner (𝕜 := ℝ) (contDiff_fderiv_apply hφ (dir 0)).continuous
    ((Tm P).contDiff.comp (contDiff_fderiv_apply hφ (dir 1))).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_inner_left (hasCompactSupport_fderiv_apply hc (dir 0)))

/-- **Gårding's identity.**  For a Dirac-type operator `P = P₀ ∂₀ + P₁ ∂₁` on smooth compactly
supported functions, `‖∇φ‖₂ = ‖P φ‖₂`. -/
theorem garding [CompleteSpace X] {P : Fin 2 → X →L[ℝ] X} (hP : DiracPair P) {φ : ℂ → X}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, (‖fderiv ℝ φ z (dir 0)‖ ^ 2 + ‖fderiv ℝ φ z (dir 1)‖ ^ 2) =
      ∫ z, ‖∑ j, P j (fderiv ℝ φ z (dir j))‖ ^ 2 := by
  have hpt : (fun z => ‖∑ j, P j (fderiv ℝ φ z (dir j))‖ ^ 2) = fun z =>
      (‖fderiv ℝ φ z (dir 0)‖ ^ 2 + ‖fderiv ℝ φ z (dir 1)‖ ^ 2) +
        2 * ⟪fderiv ℝ φ z (dir 0), Tm P (fderiv ℝ φ z (dir 1))⟫_ℝ := by
    funext z
    rw [Fin.sum_univ_two]
    exact norm_sum_sq hP _ _
  rw [hpt]
  have i12 : Integrable fun z => ‖fderiv ℝ φ z (dir 0)‖ ^ 2 + ‖fderiv ℝ φ z (dir 1)‖ ^ 2 :=
    (integrable_norm_sq_fderiv hφ hc _).add (integrable_norm_sq_fderiv hφ hc _)
  rw [integral_add i12 ((integrable_cross (P := P) hφ hc).const_mul 2), integral_const_mul,
    cross_integral hP hφ hc, mul_zero, add_zero]

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
