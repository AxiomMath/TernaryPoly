module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ConjInvariance

@[expose] public section


/-!
# Restriction to conjugate subgroups

Formalized by Claude Sonnet 5.5.

If `ι : K →* G` and `ι' : K' →* G` are related by a homomorphism `φ : K' →* K` with `ι (φ s) = g ι' s g⁻¹`, then the restriction of a class of `H²(G, A)` along `ι'` is the
transport, along `φ` with the coefficient comparison `ρ(g⁻¹)`, of its restriction along `ι`.  This is the independence of the orbit representative for the restriction to the
stabilizer of a point of a `G`-set, and follows from the triviality of inner automorphisms (`h2Map_conj_self`).
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem res_conj {G K K' : Type} [Group G] [Group K] [Group K'] (A : Rep ℂ G) (g : G) (ι : K →* G)
    (ι' : K' →* G) (φ : K' →* K) (hφ : ∀ s, ι (φ s) = g * ι' s * g⁻¹)
    (hT : ∀ (s : K') (v : Rep.res ι A), (A.ρ g⁻¹) ((Rep.res ι A).ρ (φ s) v) = (Rep.res ι' A).ρ s ((A.ρ g⁻¹) v))
    (c : groupCohomology.H2 A) :
    EdgeNat.h2Map φ (Rep.res ι A) (Rep.res ι' A) (A.ρ g⁻¹) hT (twoCohomologyRestriction ι A c) =
      twoCohomologyRestriction ι' A c := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective A c
  have hinn := h2Map_conj_self A g (groupCohomology.H2π A z)
  rw [EdgeNat.h2Map_π] at hinn
  have h1 := congrArg (twoCohomologyRestriction ι' A) hinn
  rw [twoCohomologyRestriction_apply, twoCohomologyRestriction_apply] at h1
  rw [twoCohomologyRestriction_apply, EdgeNat.h2Map_π, twoCohomologyRestriction_apply]
  rw [← h1]
  congr 1
  apply Subtype.ext
  funext x
  obtain ⟨a, b⟩ := x
  change A.ρ g⁻¹ (z.1 (ι (φ a), ι (φ b))) = A.ρ g⁻¹ (z.1 (g * ι' a * g⁻¹, g * ι' b * g⁻¹))
  rw [hφ a, hφ b]

end TernaryPeriodPolynomials.Argument.GammaNStokes
