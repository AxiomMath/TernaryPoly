module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.TwistKoszul

@[expose] public section


/-!
# The cuspidal groups under a conjugation of the Levi

Formalized by Claude Sonnet 5.5.

Let `α` be an automorphism of `Γ = Γ(N)` which is conjugation by a matrix `A ∈ GL₂(ℚ)`, and let `Ξ : V₁ → V₂` satisfy `Ξ (ρ₁(α l) v) = ρ₂(l) (Ξ v)`.  The cohomology map `cuspXiH1` (`c ↦ Ξ ∘ c ∘ α`) carries the cuspidal subspace of `H¹(Γ, V₁)`
into that of `H¹(Γ, V₂)` (`cuspXiH1_mem`): the stabilizer of the cusp `F · ∞` is mapped by `α` into the stabilizer of the cusp `A F · ∞`.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace leviCuspStab mem_cuspidalSubspace_π)

variable {Λ : Subgroup SL(2, ℤ)} (α : Λ ≃* Λ) (A : GL (Fin 2) ℚ)
  (hα : ∀ g : Λ, Matrix.SpecialLinearGroup.mapGL ℚ (α g).1 = A * Matrix.SpecialLinearGroup.mapGL ℚ g.1 * A⁻¹)
  (V₁ V₂ : Rep ℂ Λ) (Ξ : V₁ →ₗ[ℂ] V₂) (hΞ : ∀ l v, Ξ (V₁.ρ (α l) v) = V₂.ρ l (Ξ v))

include hΞ in
theorem cuspInter (l : Λ) : (V₂.ρ l).comp Ξ = Ξ.comp (V₁.ρ (α.toMonoidHom l)) :=
  LinearMap.ext fun v => (hΞ l v).symm

/-- **The transport `H¹(Λ, V₁) → H¹(Λ, V₂)`**, `c ↦ Ξ ∘ c ∘ α`. -/
def cuspXiH1 : groupCohomology.H1 V₁ →ₗ[ℂ] groupCohomology.H1 V₂ :=
  oneCocyclePullbackH1 V₁ V₂ α.toMonoidHom Ξ (cuspInter α V₁ V₂ Ξ hΞ)

theorem cuspXiH1_π (c : groupCohomology.cocycles₁ V₁) :
    cuspXiH1 α V₁ V₂ Ξ hΞ (groupCohomology.H1π V₁ c) = groupCohomology.H1π V₂
      (oneCocyclePullback V₁ V₂ α.toMonoidHom Ξ (cuspInter α V₁ V₂ Ξ hΞ) c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

include hα in
theorem leviCuspStab_map (F : GL (Fin 2) ℚ) (γ : leviCuspStab Λ F) : α γ.1 ∈ leviCuspStab Λ (A * F) := by
  have h := γ.2
  change ((F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ.1.1 * F : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 at h
  change (((A * F)⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (α γ.1).1 * (A * F) : GL (Fin 2) ℚ) :
    Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0
  rw [hα]
  have e : (A * F)⁻¹ * (A * Matrix.SpecialLinearGroup.mapGL ℚ γ.1.1 * A⁻¹) * (A * F) =
      F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ.1.1 * F := by group
  rw [e]
  exact h

include hα in
/-- **The transport preserves the cuspidal subspace.** -/
theorem cuspXiH1_mem (x : groupCohomology.H1 V₁) (hx : x ∈ cuspidalSubspace Λ V₁) :
    cuspXiH1 α V₁ V₂ Ξ hΞ x ∈ cuspidalSubspace Λ V₂ := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [cuspXiH1_π, mem_cuspidalSubspace_π]
    rw [mem_cuspidalSubspace_π] at hx
    intro F
    obtain ⟨u, hu⟩ := hx (A * F)
    refine ⟨Ξ u, fun γ => ?_⟩
    have h1 := hu ⟨α γ.1, leviCuspStab_map α A hα F γ⟩
    change Ξ (c.1 (α γ.1)) = V₂.ρ γ.1 (Ξ u) - Ξ u
    rw [h1, map_sub, hΞ]

end TernaryPeriodPolynomials.Argument.FrameInvariance
