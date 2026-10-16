module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.Bootstrap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section


/-!
# The two-dimensional sup-norm estimate

For a smooth compactly supported `ψ : ℂ → X`, `‖ψ z‖ ≤ ∫ ‖∂₀ ∂₁ ψ‖`: a Sobolev inequality in the
plane, proved by integrating along the two coordinate lines.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section Sup

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem line_hasDerivAt {g : ℂ → X} (hg : Differentiable ℝ g) (p e : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => g (p + t • e)) (fderiv ℝ g (p + t • e) e) t := by
  have h1 : HasDerivAt (fun t : ℝ => p + t • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add p
  exact (hg (p + t • e)).hasFDerivAt.comp_hasDerivAt t h1

omit [InnerProductSpace ℝ X] [CompleteSpace X] in
theorem line_compact {g : ℂ → X} (hc : HasCompactSupport g) (p e : ℂ) (he : e ≠ 0) :
    HasCompactSupport fun t : ℝ => g (p + t • e) := by
  have hemb : Topology.IsClosedEmbedding fun t : ℝ => p + t • e := by
    have h1 : Topology.IsClosedEmbedding fun t : ℝ => t • e :=
      (LinearMap.isClosedEmbedding_of_injective (f := (LinearMap.toSpanSingleton ℝ ℂ e))
        (LinearMap.ker_eq_bot.mpr (fun a b hab => by simpa [he] using hab)))
    exact (Homeomorph.addLeft p).isClosedEmbedding.comp h1
  exact hc.comp_isClosedEmbedding hemb

/-- The point `r + i t` of the plane. -/
def mk (r t : ℝ) : ℂ := r • (1 : ℂ) + t • Complex.I

theorem mk_re_im (z : ℂ) : mk z.re z.im = z := by
  apply Complex.ext <;> simp [mk]

omit [CompleteSpace X] in
/-- **The `L¹` bound for the sup norm.**  For smooth compactly supported `ψ`,
`‖ψ z‖ ≤ ∫ ‖∂₀ ∂₁ ψ‖`. -/
theorem enorm_le_lintegral_D01 {ψ : ℂ → X} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (z : ℂ) :
    ‖ψ z‖ₑ ≤ ∫⁻ w, ‖fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1)) w (dir 0)‖ₑ := by
  have hψ₁ : ContDiff ℝ ∞ fun z => fderiv ℝ ψ z (dir 1) := contDiff_fderiv_apply hψ _
  have hc₁ : HasCompactSupport fun z => fderiv ℝ ψ z (dir 1) := hasCompactSupport_fderiv_apply hc _
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have step2 : ∀ t : ℝ, ‖fderiv ℝ ψ (mk z.re t) (dir 1)‖ₑ ≤
      ∫⁻ r : ℝ, ‖fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1)) (mk r t) (dir 0)‖ₑ := by
    intro t
    have hd : ∀ r : ℝ, deriv (fun r : ℝ => (fun z => fderiv ℝ ψ z (dir 1)) ((t • Complex.I) + r • (1 : ℂ))) r =
        fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1)) (mk r t) (dir 0) := fun r => by
      have := (line_hasDerivAt (hψ₁.differentiable (by simp)) (t • Complex.I) 1 r).deriv
      rw [this]
      simp only [dir, ite_eq_left]
      congr 2
      simp only [mk]
      abel
    have hcl : HasCompactSupport fun r : ℝ => (fun z => fderiv ℝ ψ z (dir 1)) ((t • Complex.I) + r • (1 : ℂ)) :=
      line_compact hc₁ _ _ one_ne_zero
    have hsm : ContDiff ℝ 1 fun r : ℝ => (fun z => fderiv ℝ ψ z (dir 1)) ((t • Complex.I) + r • (1 : ℂ)) :=
      (hψ₁.comp (contDiff_const.add (contDiff_id.smul contDiff_const))).of_le (by simp)
    have := hcl.enorm_le_lintegral_Ici_deriv hsm z.re
    simp only [hd] at this
    have e1 : (t • Complex.I) + z.re • (1 : ℂ) = mk z.re t := add_comm _ _
    rw [e1] at this
    exact this.trans (setLIntegral_le_lintegral _ _)
  have hdψ : ∀ t : ℝ, deriv (fun t : ℝ => ψ (z.re • (1 : ℂ) + t • Complex.I)) t =
      fderiv ℝ ψ (mk z.re t) (dir 1) := fun t => by
    have := (line_hasDerivAt (hψ.differentiable (by simp)) (z.re • (1 : ℂ)) Complex.I t).deriv
    rw [this]
    simp only [dir, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
    rfl
  have hclψ : HasCompactSupport fun t : ℝ => ψ (z.re • (1 : ℂ) + t • Complex.I) :=
    line_compact hc _ _ Complex.I_ne_zero
  have hsmψ : ContDiff ℝ 1 fun t : ℝ => ψ (z.re • (1 : ℂ) + t • Complex.I) :=
    (hψ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))).of_le (by simp)
  have h1 := hclψ.enorm_le_lintegral_Ici_deriv hsmψ z.im
  simp only [hdψ] at h1
  have e2 : z.re • (1 : ℂ) + z.im • Complex.I = z := mk_re_im z
  rw [e2] at h1
  refine h1.trans ((setLIntegral_le_lintegral _ _).trans ?_)
  refine (lintegral_mono step2).trans (le_of_eq ?_)
  -- change of variables
  have hD : Continuous fun w => fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1)) w (dir 0) :=
    (contDiff_fderiv_apply hψ₁ (dir 0)).continuous
  have hmeas : Measurable fun p : ℝ × ℝ => ‖fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1))
      (mk p.1 p.2) (dir 0)‖ₑ := by
    have hmk : Continuous fun p : ℝ × ℝ => mk p.1 p.2 := by
      unfold mk
      fun_prop
    exact (hD.comp hmk).enorm.measurable
  have hsymm : ∀ p : ℝ × ℝ, Complex.measurableEquivRealProd.symm p = mk p.1 p.2 := fun p => by
    apply Complex.ext <;> simp [mk]
  have h := (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    (fun w => ‖fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1)) w (dir 0)‖ₑ)
  simp only [hsymm] at h
  rw [← h, Measure.volume_eq_prod, lintegral_prod_symm _ hmeas.aemeasurable]

omit [CompleteSpace X] in
theorem norm_le_integral_D01 {ψ : ℂ → X} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (z : ℂ) :
    ‖ψ z‖ ≤ ∫ w, ‖fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1)) w (dir 0)‖ := by
  have hD : ContDiff ℝ ∞ fun w => fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1)) w (dir 0) :=
    contDiff_fderiv_apply (contDiff_fderiv_apply hψ _) _
  have hDk : HasCompactSupport fun w => fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1)) w (dir 0) :=
    hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hc _) _
  have hi : Integrable fun w => ‖fderiv ℝ (fun z => fderiv ℝ ψ z (dir 1)) w (dir 0)‖ :=
    (hD.continuous.integrable_of_hasCompactSupport hDk).norm
  have h := enorm_le_lintegral_D01 hψ hc z
  rw [← ofReal_integral_norm_eq_lintegral_enorm (hD.continuous.integrable_of_hasCompactSupport hDk),
    ← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => norm_nonneg _)).mp h

end Sup

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
