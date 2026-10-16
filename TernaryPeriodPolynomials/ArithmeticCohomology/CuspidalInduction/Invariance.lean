module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Integrand

@[expose] public section


/-!
# Invariance of the cup-form integrand under the group

Formalized by Claude Sonnet 5.5.

For twisted cusp functions `Φ(γx) = ρ(γ)Φ(x) + f(γ)`, `Φ'(γx) = ρ'(γ)Φ'(x) + f'(γ)` and a `Γ`-invariant pairing, the triangle integrand is
`Γ`-invariant: `integ ε Φ Φ' (γ y) = integ ε Φ Φ' y`.  Hence the cup form is a sum over `Γ`-orbits of triangles, independent of the representatives.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

variable {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A'] {Γ : Subgroup IntegralGL}

/-- **The integrand is invariant** under the group, for twisted cusp functions and an invariant pairing. -/
theorem integ_invariant (hSL : ∀ g ∈ Γ, IsSL g) {ρ : Representation ℂ Γ A} {ρ' : Representation ℂ Γ A'}
    (ε : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ) (hε : ∀ (γ : Γ) v w, ε (ρ γ v) (ρ' γ w) = ε v w)
    (Φ : RationalLine2 → A) (Φ' : RationalLine2 → A') (f : Γ → A) (f' : Γ → A')
    (hΦ : ∀ (γ : Γ) (x : RationalLine2), Φ ((γ : IntegralGL) • x) = ρ γ (Φ x) + f γ)
    (hΦ' : ∀ (γ : Γ) (x : RationalLine2), Φ' ((γ : IntegralGL) • x) = ρ' γ (Φ' x) + f' γ)
    (γ : Γ) (y : Tri) : integ ε Φ Φ' ((γ : IntegralGL) • y) = integ ε Φ Φ' y := by
  rw [← integ_comp ε Φ Φ' (hSL γ γ.2) y]
  have e1 : (fun c => Φ ((γ : IntegralGL) • c)) = fun c => ρ γ (Φ c) + f γ := funext (hΦ γ)
  have e2 : (fun c => Φ' ((γ : IntegralGL) • c)) = fun c => ρ' γ (Φ' c) + f' γ := funext (hΦ' γ)
  rw [e1, e2, integ_add_const]
  unfold integ
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [hε, hε]

end TernaryPeriodPolynomials.Argument.CuspidalInduction
