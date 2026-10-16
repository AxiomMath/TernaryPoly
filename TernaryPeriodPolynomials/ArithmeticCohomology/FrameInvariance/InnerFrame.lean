module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ConjInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeMackey
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.FrameChange

@[expose] public section


/-!
# Global classes are invariant under conjugation of the face groups

Formalized by Claude Sonnet 5.5.

`res_h2Map_inner`: let `ι₁ : K₁ → G`, `ι₂ : K₂ → G` be subgroups and `θ : K₂ → K₁` with `ι₁ (θ k) = g ι₂(k) g⁻¹` for an element `g ∈ G`.  Then the transport along `θ` (coefficient map `ρ(g⁻¹)`) of the restriction `res_{K₁} c` of a class
`c ∈ H²(G, A)` is `res_{K₂} c` (inner automorphisms act trivially on `H²(G, A)`, the `h2Map_conj_self`).  `repEquiv ρ g` is `ρ(g⁻¹)` as a linear equivalence.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes

section Inner

variable {G K₁ K₂ : Type} [Group G] [Group K₁] [Group K₂] (A : Rep ℂ G) (g : G) (ι₁ : K₁ →* G) (ι₂ : K₂ →* G)
  (θ : K₂ →* K₁) (hθ : ∀ k, ι₁ (θ k) = g * ι₂ k * g⁻¹)

/-- `ρ(g⁻¹)` as a linear equivalence of the representation space. -/
def repEquiv : A ≃ₗ[ℂ] A :=
  LinearEquiv.ofLinearMap (A.ρ g⁻¹) (A.ρ g) (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl)

theorem repEquiv_apply (v : A) : repEquiv A g v = A.ρ g⁻¹ v := rfl

include hθ in
theorem hT_inner (k : K₂) (v : Rep.res ι₁ A) :
    repEquiv A g ((Rep.res ι₁ A).ρ (θ k) v) = (Rep.res ι₂ A).ρ k (repEquiv A g v) := by
  change A.ρ g⁻¹ (A.ρ (ι₁ (θ k)) v) = A.ρ (ι₂ k) (A.ρ g⁻¹ v)
  rw [hθ]
  exact innerConj_hT A g (ι₂ k) v

include hθ in
/-- **Restriction of a global class and conjugation of the face group**. -/
theorem res_h2Map_inner (c : groupCohomology.H2 A) :
    EdgeNat.h2Map θ (Rep.res ι₁ A) (Rep.res ι₂ A) (repEquiv A g).toLinearMap (hT_inner A g ι₁ ι₂ θ hθ)
        (twoCohomologyRestriction ι₁ A c) = twoCohomologyRestriction ι₂ A c := by
  have e := EdgeNat.restriction_h2Map (innerConjHom g) A A (A.ρ g⁻¹) (innerConj_hT A g) ι₁ ι₂ θ
    (fun k => (hθ k).symm) c
  rw [h2Map_conj_self] at e
  exact e.symm

end Inner

end TernaryPeriodPolynomials.Argument.FrameInvariance
