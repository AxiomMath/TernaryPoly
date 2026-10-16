module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.Quotient
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

@[expose] public section


/-!
# General coercivity: unfolding integrals over the orbit space

If `ψ` is a function on `Space` whose translates sum to one over the support of `F`, then the integral
of `F` over the orbit space equals the integral of `ψ · (F ∘ proj)` over `Space`.  This is the
unfolding formula behind the integration-by-parts identities on the orbit space.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering
open scoped ENNReal

variable {Γ : Subgroup RealGL}

/-- Unfolding: `∫_{X_Γ} F = ∫_{Space} ψ · F ∘ proj` whenever the `Γ`-translates of `ψ` sum to one
wherever `F ∘ proj` is nonzero, and `ψ · F ∘ proj` is integrable. -/
theorem Admissible.integral_unfold (h : Admissible Γ) {F : OrbitSpace Γ → ℝ} (hF : Measurable F)
    {ψ : Space → ℝ} (hψ : Measurable ψ)
    (hpart : ∀ S : Space, F (proj Γ S) ≠ 0 → ∑' γ : Γ, ψ (γ • S) = 1)
    (hint : Integrable (fun S => ψ S * F (proj Γ S)) spaceVolume) :
    ∫ q, F q ∂quotientVolume Γ = ∫ S, ψ S * F (proj Γ S) ∂spaceVolume := by
  have : Countable Γ := h.countable
  obtain ⟨t, htm, ht⟩ := h.exists_isFundamentalDomain
  set f : Space → ℝ := fun S => ψ S * F (proj Γ S) with hf
  have hfm : Measurable f := hψ.mul (hF.comp (measurable_quotient_mk' (s := MulAction.orbitRel Γ Space)))
  have h1 : ∫ q, F q ∂quotientVolume Γ = ∫ x in t, F (proj Γ x) ∂spaceVolume :=
    h.integral_quotientVolume ht hF
  have h2 : ∫ S, f S ∂spaceVolume = ∑' g : Γ, ∫ x in t, f (g • x) ∂spaceVolume :=
    ht.integral_eq_tsum'' f hint
  have hsm : ∀ g : Γ, Measurable (fun x : Space => f (g • x)) := fun g =>
    hfm.comp (measurable_const_smul g)
  have h3 : ∑' g : Γ, ∫ x in t, f (g • x) ∂spaceVolume =
      ∫ x in t, ∑' g : Γ, f (g • x) ∂spaceVolume := by
    symm
    apply integral_tsum (fun g => (hsm g).aestronglyMeasurable)
    have := ht.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)
    rw [← this]
    exact hint.hasFiniteIntegral.ne
  have h4 : ∀ x : Space, ∑' g : Γ, f (g • x) = F (proj Γ x) := by
    intro x
    by_cases hx : F (proj Γ x) = 0
    · simp [hf, proj_smul, hx]
    · have : ∀ g : Γ, f (g • x) = ψ (g • x) * F (proj Γ x) := fun g => by
        simp only [hf, proj_smul]
      simp only [this]
      rw [tsum_mul_right, hpart x hx, one_mul]
  rw [h1, h2, h3]
  exact setIntegral_congr_fun htm (fun x _ => (h4 x).symm)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
