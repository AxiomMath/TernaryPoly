module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CuspXi
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Pairing

@[expose] public section


/-!
# The statement of the conjugation naturality of the cup-form pairing (`CuspConjNat`)

Formalized by Claude Sonnet 5.5.

`GLConj hN α A`: the automorphism `α` of `Γ(N)` is conjugation by `A ∈ GL₂(ℤ)` (as elements of `gammaNGL N`).  `cuspXi` is the induced transport `𝒞(V₁) → 𝒞(V₂)` (`c ↦ Ξ ∘ c ∘ α`) of the cuspidal groups.
`CuspConjNat N hN` is the NATURALITY STATEMENT with the orientation sign: if `B₁`, `B₂` are cup-form pairings for the invariant pairings `e₁`, `e₂` and `e₂ (Ξ v) (Ξ' w) = ε e₁ v w`, then
`B₂ (Ξ̃ x) (Ξ̃' y) = ε · det(A) · B₁ x y`.  For `det A = -1` the factor `-1` is the reversal of the orientation of the modular curve (the Farey differential `cupForm` is skew under the swap of head and tail).
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol

variable {N : ℕ}

/-- The rational matrix of an integral `GL₂` element. -/
def AQ (A : IntegralGL) : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) A

/-- **`α` is conjugation by `A`**, in the group `gammaNGL N ≤ GL₂(ℤ)`. -/
def GLConj (hN : 3 ≤ N) (α : Gamma N ≃* Gamma N) (A : IntegralGL) : Prop :=
  ∀ l : Gamma N, ((gammaEquiv hN (α l) : gammaNGL N) : IntegralGL) = A * ((gammaEquiv hN l : gammaNGL N) : IntegralGL) * A⁻¹

theorem GLConj.mapGL {hN : 3 ≤ N} {α : Gamma N ≃* Gamma N} {A : IntegralGL} (h : GLConj hN α A) (l : Gamma N) :
    Matrix.SpecialLinearGroup.mapGL ℚ (α l).1 = AQ A * Matrix.SpecialLinearGroup.mapGL ℚ l.1 * (AQ A)⁻¹ := by
  have key : ∀ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.mapGL ℚ γ =
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (Matrix.SpecialLinearGroup.toGL γ) := fun γ => by
    ext i j
    simp [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL]
  have h1 := h l
  rw [gammaEquiv_coe, gammaEquiv_coe] at h1
  rw [key, key, h1, AQ, map_mul, map_mul, map_inv]

/-- **The transport `𝒞(V₁) → 𝒞(V₂)`, `c ↦ Ξ ∘ c ∘ α`.** -/
def cuspXi (hN : 3 ≤ N) (α : Gamma N ≃* Gamma N) (A : IntegralGL) (hα : GLConj hN α A) (V₁ V₂ : Rep ℂ (Gamma N))
    (Ξ : V₁ →ₗ[ℂ] V₂) (hΞ : ∀ l v, Ξ (V₁.ρ (α l) v) = V₂.ρ l (Ξ v)) :
    cuspidalSubspace (Gamma N) V₁ →ₗ[ℂ] cuspidalSubspace (Gamma N) V₂ :=
  ((cuspXiH1 α V₁ V₂ Ξ hΞ).comp (cuspidalSubspace (Gamma N) V₁).subtype).codRestrict _
    (fun x => cuspXiH1_mem α (AQ A) hα.mapGL V₁ V₂ Ξ hΞ x.1 x.2)

theorem cuspXi_val (hN : 3 ≤ N) (α : Gamma N ≃* Gamma N) (A : IntegralGL) (hα : GLConj hN α A) (V₁ V₂ : Rep ℂ (Gamma N))
    (Ξ : V₁ →ₗ[ℂ] V₂) (hΞ : ∀ l v, Ξ (V₁.ρ (α l) v) = V₂.ρ l (Ξ v)) (x : cuspidalSubspace (Gamma N) V₁) :
    ((cuspXi hN α A hα V₁ V₂ Ξ hΞ x : cuspidalSubspace (Gamma N) V₂) : groupCohomology.H1 V₂) =
      cuspXiH1 α V₁ V₂ Ξ hΞ x.1 := rfl

/-- **`CuspConjNat`: the cup-form pairing is natural under conjugation by `A ∈ GL₂(ℤ)`, up to the orientation sign `det A`.** -/
def CuspConjNat (N : ℕ) (hN : 3 ≤ N) : Prop :=
  ∀ (α : Gamma N ≃* Gamma N) (A : IntegralGL) (hα : GLConj hN α A)
    (V₁ V₁' V₂ V₂' : Rep ℂ (Gamma N)) [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₁']
    [FiniteDimensional ℂ V₂] [FiniteDimensional ℂ V₂']
    (e₁ : V₁ →ₗ[ℂ] V₁' →ₗ[ℂ] ℂ) (hinv₁ : ∀ (γ : Gamma N) v w, e₁ (V₁.ρ γ v) (V₁'.ρ γ w) = e₁ v w)
    (hL₁ : ∀ v, (∀ w, e₁ v w = 0) → v = 0) (hR₁ : ∀ w, (∀ v, e₁ v w = 0) → w = 0)
    (e₂ : V₂ →ₗ[ℂ] V₂' →ₗ[ℂ] ℂ) (hinv₂ : ∀ (γ : Gamma N) v w, e₂ (V₂.ρ γ v) (V₂'.ρ γ w) = e₂ v w)
    (hL₂ : ∀ v, (∀ w, e₂ v w = 0) → v = 0) (hR₂ : ∀ w, (∀ v, e₂ v w = 0) → w = 0)
    (B₁ : cuspidalSubspace (Gamma N) V₁ →ₗ[ℂ] cuspidalSubspace (Gamma N) V₁' →ₗ[ℂ] ℂ)
    (B₂ : cuspidalSubspace (Gamma N) V₂ →ₗ[ℂ] cuspidalSubspace (Gamma N) V₂' →ₗ[ℂ] ℂ)
    (_ : IsCupPairing hN V₁ V₁' e₁ hinv₁ hL₁ hR₁ B₁) (_ : IsCupPairing hN V₂ V₂' e₂ hinv₂ hL₂ hR₂ B₂)
    (Ξ : V₁ →ₗ[ℂ] V₂) (Ξ' : V₁' →ₗ[ℂ] V₂') (hΞ : ∀ l v, Ξ (V₁.ρ (α l) v) = V₂.ρ l (Ξ v))
    (hΞ' : ∀ l v, Ξ' (V₁'.ρ (α l) v) = V₂'.ρ l (Ξ' v))
    (ε : ℂ) (_ : ∀ v w, e₂ (Ξ v) (Ξ' w) = ε * e₁ v w) (x : cuspidalSubspace (Gamma N) V₁)
    (y : cuspidalSubspace (Gamma N) V₁'),
    B₂ (cuspXi hN α A hα V₁ V₂ Ξ hΞ x) (cuspXi hN α A hα V₁' V₂' Ξ' hΞ' y) = ε * ((A.val.det : ℤ) : ℂ) * B₁ x y

end TernaryPeriodPolynomials.Argument.FrameInvariance
