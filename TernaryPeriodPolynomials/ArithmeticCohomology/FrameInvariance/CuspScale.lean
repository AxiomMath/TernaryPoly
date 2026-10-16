module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CuspConjNat

@[expose] public section


/-!
# Scaling of the cup-form pairing under an equivariant map of coefficient modules

Formalized by Claude Sonnet 5.5.

`cuspConjNat` with the identity automorphism `α = id` and `A = 1`: if `Ξ : V₁ → V₂`, `Ξ' : V₁' → V₂'` are `Γ(N)`-equivariant and `e₂(Ξ v, Ξ' w) = ε e₁(v, w)`, then
`B₂(Ξ_* x, Ξ'_* y) = ε B₁(x, y)` for cup-form pairings `B₁`, `B₂`.  This covers `x ↦ x ⊗ u`, `y ↦ y ⊗ u'` for invariant vectors `u, u'` of a permutation module
(`ε = ⟨u, u'⟩`), the scaling used when descending the canonical face pairing to a finite-index subgroup.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPoly.RankTwoAugmentedFrames

variable {N : ℕ}

theorem glConj_refl (hN : 3 ≤ N) : GLConj hN (MulEquiv.refl (Gamma N)) 1 := by
  intro l
  simp

/-- **The induced map on the cuspidal groups of an equivariant map of coefficient modules** (`cuspXi` for `α = id`, `A = 1`). -/
def cuspMap (hN : 3 ≤ N) (V₁ V₂ : Rep ℂ (Gamma N)) (Ξ : V₁ →ₗ[ℂ] V₂)
    (hΞ : ∀ l v, Ξ (V₁.ρ l v) = V₂.ρ l (Ξ v)) :
    cuspidalSubspace (Gamma N) V₁ →ₗ[ℂ] cuspidalSubspace (Gamma N) V₂ :=
  cuspXi hN (MulEquiv.refl (Gamma N)) 1 (glConj_refl hN) V₁ V₂ Ξ (fun l v => hΞ l v)

/-- **`cuspMap` scales the cup-form pairings by `ε`.** -/
theorem cuspMap_pairing (hN : 3 ≤ N) (V₁ V₁' V₂ V₂' : Rep ℂ (Gamma N)) [FiniteDimensional ℂ V₁]
    [FiniteDimensional ℂ V₁'] [FiniteDimensional ℂ V₂] [FiniteDimensional ℂ V₂']
    (e₁ : V₁ →ₗ[ℂ] V₁' →ₗ[ℂ] ℂ) (hinv₁ : ∀ (γ : Gamma N) v w, e₁ (V₁.ρ γ v) (V₁'.ρ γ w) = e₁ v w)
    (hL₁ : ∀ v, (∀ w, e₁ v w = 0) → v = 0) (hR₁ : ∀ w, (∀ v, e₁ v w = 0) → w = 0)
    (e₂ : V₂ →ₗ[ℂ] V₂' →ₗ[ℂ] ℂ) (hinv₂ : ∀ (γ : Gamma N) v w, e₂ (V₂.ρ γ v) (V₂'.ρ γ w) = e₂ v w)
    (hL₂ : ∀ v, (∀ w, e₂ v w = 0) → v = 0) (hR₂ : ∀ w, (∀ v, e₂ v w = 0) → w = 0)
    (B₁ : cuspidalSubspace (Gamma N) V₁ →ₗ[ℂ] cuspidalSubspace (Gamma N) V₁' →ₗ[ℂ] ℂ)
    (B₂ : cuspidalSubspace (Gamma N) V₂ →ₗ[ℂ] cuspidalSubspace (Gamma N) V₂' →ₗ[ℂ] ℂ)
    (h₁ : IsCupPairing hN V₁ V₁' e₁ hinv₁ hL₁ hR₁ B₁) (h₂ : IsCupPairing hN V₂ V₂' e₂ hinv₂ hL₂ hR₂ B₂)
    (Ξ : V₁ →ₗ[ℂ] V₂) (Ξ' : V₁' →ₗ[ℂ] V₂') (hΞ : ∀ l v, Ξ (V₁.ρ l v) = V₂.ρ l (Ξ v))
    (hΞ' : ∀ l v, Ξ' (V₁'.ρ l v) = V₂'.ρ l (Ξ' v)) (ε : ℂ) (hε : ∀ v w, e₂ (Ξ v) (Ξ' w) = ε * e₁ v w)
    (x : cuspidalSubspace (Gamma N) V₁) (y : cuspidalSubspace (Gamma N) V₁') :
    B₂ (cuspMap hN V₁ V₂ Ξ hΞ x) (cuspMap hN V₁' V₂' Ξ' hΞ' y) = ε * B₁ x y := by
  have h := cuspConjNat N hN (MulEquiv.refl (Gamma N)) 1 (glConj_refl hN) V₁ V₁' V₂ V₂' e₁ hinv₁ hL₁ hR₁ e₂
    hinv₂ hL₂ hR₂ B₁ B₂ h₁ h₂ Ξ Ξ' (fun l v => hΞ l v) (fun l v => hΞ' l v) ε hε x y
  rw [cuspMap, cuspMap, h]
  simp

end TernaryPeriodPolynomials.Argument.FrameInvariance
