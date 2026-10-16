module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalPairing

@[expose] public section


/-!
# The compact-support map `H¹_c → H¹` of `Γ(N)` and its image: the cuspidal subspace

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`, ("the long exact sequence for
a compactified modular curve identifies cuspidal cohomology with the image of compactly supported cohomology").

In the Farey model of the compactified modular curve, `H¹_c(A) = ker d_c(A)` (the compactly supported Farey cocycles).  `jTrue_exists`: for
`N ≥ 3` and a finite-dimensional `Γ(N)`-module `A` there is a linear map `j : ker d_c(A) → H¹(Γ(N), A)` (Mathlib's `groupCohomology.H1`)
such that
* `j (dΦ) = [fTw Φ]` for every normalized twisted cusp function `Φ` (`Φ(γ x) = γ Φ(x) + f(γ)`, `Φ(cusp₁) = 0`): the class of the
  cocycle `γ ↦ Φ(γ ∞)`; every compactly supported Farey cocycle is of this form;
* `range j` is exactly the cuspidal subspace `cuspidalSub A` (the classes with zero restriction to the stabilizer of every cusp);
* `ker j` is exactly `∂ H⁰(cusps)`: the Farey differentials `dΦ` of strictly equivariant cusp functions `Φ` (the image of `H⁰` of the
  boundary components).
This is the exact sequence `H⁰(∂) → H¹_c → H¹ → H¹(∂)` at `H¹_c` and `H¹`; `j` is *not* the naive edge-identity map.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol Module
open scoped Classical

section JTrue

variable {N : ℕ}

/-- The dual representation as a `Rep`. -/
def dualRep (A : Rep ℂ (gammaNGL N)) : Rep ℂ (gammaNGL N) := Rep.of A.ρ.dual

instance (A : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A] : FiniteDimensional ℂ (dualRep A) :=
  inferInstanceAs (FiniteDimensional ℂ (Module.Dual ℂ A))

theorem jTrue_exists (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A] :
    ∃ j : LinearMap.ker (dc A.ρ) →ₗ[ℂ] groupCohomology.H1 A,
      (∀ (Φ : Tw A.ρ) (_ : Φ.1 cusp1 = 0), ∃ h : bdryTw A.ρ hN Φ ∈ LinearMap.ker (dc A.ρ),
        j ⟨bdryTw A.ρ hN Φ, h⟩ = mTw A Φ) ∧
      (∀ F : LinearMap.ker (dc A.ρ), ∃ Φ : Tw A.ρ, Φ.1 cusp1 = 0 ∧ bdryTw A.ρ hN Φ = F.1) ∧
      LinearMap.range j = cuspidalSub A ∧
      (∀ F : LinearMap.ker (dc A.ρ), j F = 0 ↔ F.1 ∈ LinearMap.range (bdryEq hN A.ρ)) := by
  have := c1_finite (ρ := A.ρ) (gammaNFareyData hN)
  have := c1_finite (ρ := (dualRep A).ρ) (gammaNFareyData hN)
  obtain ⟨-, hKA, -⟩ := cuspidal_dims hN A (dualRep A) (dualCoupling A.ρ)
  let h' : Tn A.ρ →ₗ[ℂ] LinearMap.ker (dc A.ρ) :=
    LinearMap.codRestrict (LinearMap.ker (dc A.ρ)) (hT hN A.ρ) (fun Φ => range_hT_le hN A ⟨Φ, rfl⟩)
  have hinj : Function.Injective h' := fun Φ Ψ h => hT_inj hN A (congrArg Subtype.val h)
  have hsurj : Function.Surjective h' := by
    rintro ⟨F, hF⟩
    rw [← hKA] at hF
    obtain ⟨Φ, rfl⟩ := hF
    exact ⟨Φ, rfl⟩
  let e : Tn A.ρ ≃ₗ[ℂ] LinearMap.ker (dc A.ρ) := LinearEquiv.ofBijective h' ⟨hinj, hsurj⟩
  let j : LinearMap.ker (dc A.ρ) →ₗ[ℂ] groupCohomology.H1 A := ((mTw A).comp (Tn A.ρ).subtype).comp e.symm.toLinearMap
  have hj : ∀ Φ : Tn A.ρ, j (e Φ) = mTw A Φ.1 := fun Φ => by simp [j]
  have he : ∀ Φ : Tn A.ρ, (e Φ).1 = bdryTw A.ρ hN Φ.1 := fun Φ => rfl
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · intro Φ h0
    refine ⟨(e ⟨Φ, mem_Tn.mpr h0⟩).2, ?_⟩
    have := hj ⟨Φ, mem_Tn.mpr h0⟩
    rw [← this]
    rfl
  · intro F
    obtain ⟨Φ, rfl⟩ := e.surjective F
    exact ⟨Φ.1, mem_Tn.mp Φ.2, (he Φ).symm⟩
  · ext x
    constructor
    · rintro ⟨F, rfl⟩
      obtain ⟨Φ, rfl⟩ := e.surjective F
      rw [hj]
      exact mTw_mem_cuspidal A Φ.1
    · intro hx
      obtain ⟨Φ, h0, hΦ⟩ := exists_Tn_of_cuspidal hN A hx
      exact ⟨e ⟨Φ, mem_Tn.mpr h0⟩, by rw [hj]; exact hΦ⟩
  · intro F
    obtain ⟨Φ, rfl⟩ := e.surjective F
    rw [hj, he, ← map_hT_ker_gq hN A]
    constructor
    · intro h0
      refine ⟨Φ, ?_, rfl⟩
      change (cohIso A (gammaNFareyData hN)).symm (mTw A Φ.1) = 0
      rw [h0, map_zero]
    · rintro ⟨Ψ, hΨ, hΨΦ⟩
      have : Ψ = Φ := hT_inj hN A hΨΦ
      subst this
      have : (cohIso A (gammaNFareyData hN)).symm (mTw A Ψ.1) = 0 := hΨ
      simpa using this

end JTrue

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
