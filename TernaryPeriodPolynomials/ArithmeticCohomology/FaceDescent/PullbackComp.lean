module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OneCocyclePullback

@[expose] public section


/-!
# Composition of the cohomology transports `oneCocyclePullbackH1`

Formalized by Claude Sonnet 5.5.

`oneCocyclePullbackH1_comp`: `P(ψ₂, T₂) ∘ P(ψ₁, T₁) = P(ψ₁ ∘ ψ₂, T₂ ∘ T₁)` for the transports `c ↦ T ∘ c ∘ ψ` of degree-one cohomology classes, and `oneCocyclePullbackH1_id` (the identity transport is the identity).  This is the functoriality
needed to turn the face symmetries into a group action.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G₁ G₂ G₃ : Type} [Group G₁] [Group G₂] [Group G₃] {A₁ : Rep ℂ G₁} {A₂ : Rep ℂ G₂} {A₃ : Rep ℂ G₃}

theorem oneCocyclePullbackH1_comp (ψ₁ : G₂ →* G₁) (T₁ : A₁ →ₗ[ℂ] A₂)
    (h₁ : ∀ g, (A₂.ρ g).comp T₁ = T₁.comp (A₁.ρ (ψ₁ g)))
    (ψ₂ : G₃ →* G₂) (T₂ : A₂ →ₗ[ℂ] A₃) (h₂ : ∀ g, (A₃.ρ g).comp T₂ = T₂.comp (A₂.ρ (ψ₂ g)))
    (ψ₃ : G₃ →* G₁) (T₃ : A₁ →ₗ[ℂ] A₃) (h₃ : ∀ g, (A₃.ρ g).comp T₃ = T₃.comp (A₁.ρ (ψ₃ g)))
    (hψ : ∀ g, ψ₁ (ψ₂ g) = ψ₃ g) (hT : ∀ v, T₂ (T₁ v) = T₃ v) (x : groupCohomology.H1 A₁) :
    oneCocyclePullbackH1 A₂ A₃ ψ₂ T₂ h₂ (oneCocyclePullbackH1 A₁ A₂ ψ₁ T₁ h₁ x) =
      oneCocyclePullbackH1 A₁ A₃ ψ₃ T₃ h₃ x := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective A₁ x
  rw [oneCocyclePullbackH1_apply, oneCocyclePullbackH1_apply, oneCocyclePullbackH1_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro g
  simp only [oneCocyclePullback_apply, hψ, hT]

theorem oneCocyclePullbackH1_id (T : A₁ →ₗ[ℂ] A₁) (h : ∀ g, (A₁.ρ g).comp T = T.comp (A₁.ρ ((MonoidHom.id G₁) g)))
    (hT : ∀ v, T v = v) (x : groupCohomology.H1 A₁) :
    oneCocyclePullbackH1 A₁ A₁ (MonoidHom.id G₁) T h x = x := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective A₁ x
  rw [oneCocyclePullbackH1_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro g
  simp only [oneCocyclePullback_apply, hT, MonoidHom.id_apply]

/-- The transport depends only on the underlying data. -/
theorem oneCocyclePullbackH1_congr (ψ ψ' : G₂ →* G₁) (T T' : A₁ →ₗ[ℂ] A₂)
    (h : ∀ g, (A₂.ρ g).comp T = T.comp (A₁.ρ (ψ g))) (h' : ∀ g, (A₂.ρ g).comp T' = T'.comp (A₁.ρ (ψ' g)))
    (hψ : ∀ g, ψ g = ψ' g) (hT : ∀ v, T v = T' v) (x : groupCohomology.H1 A₁) :
    oneCocyclePullbackH1 A₁ A₂ ψ T h x = oneCocyclePullbackH1 A₁ A₂ ψ' T' h' x := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective A₁ x
  rw [oneCocyclePullbackH1_apply, oneCocyclePullbackH1_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro g
  simp only [oneCocyclePullback_apply, hψ, hT]

/-- A transport with `ψ = id` and `T = id` is the identity. -/
theorem oneCocyclePullbackH1_of_id (ψ : G₁ →* G₁) (T : A₁ →ₗ[ℂ] A₁) (h : ∀ g, (A₁.ρ g).comp T = T.comp (A₁.ρ (ψ g)))
    (hψ : ∀ g, ψ g = g) (hT : ∀ v, T v = v) (x : groupCohomology.H1 A₁) :
    oneCocyclePullbackH1 A₁ A₁ ψ T h x = x := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective A₁ x
  rw [oneCocyclePullbackH1_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro g
  simp only [oneCocyclePullback_apply, hT, hψ]

end TernaryPeriodPolynomials.Argument.FaceDescent
