/-
Inner automorphisms act trivially on degree-two group cohomology.

For a group `G` and `A : Rep ℂ G`, the transport of `H²(G, A)` along conjugation by `g`, with the
coefficient comparison `ρ(g⁻¹)`, is the identity.  This is the standard fact (not in Mathlib) needed
to see that the restriction of an `H²` class to a conjugate subgroup, transported back by the
conjugation, does not depend on the chosen orbit representative.

Formalized by Claude Sonnet 5.5.
-/
module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EdgeNaturalityIso

@[expose] public section


open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G] (A : Rep ℂ G) (g : G)

/-- Key cocycle identity behind the triviality of inner automorphisms on `H²`. -/
theorem inner_conj_key (z : groupCohomology.cocycles₂ A) (x y : G) :
    A.ρ g⁻¹ (z.1 (g * x * g⁻¹, g * y * g⁻¹)) - z.1 (x, y) =
      A.ρ x (A.ρ g⁻¹ (z.1 (g * y * g⁻¹, g) - z.1 (g, y))) -
        A.ρ g⁻¹ (z.1 (g * (x * y) * g⁻¹, g) - z.1 (g, x * y)) +
        A.ρ g⁻¹ (z.1 (g * x * g⁻¹, g) - z.1 (g, x)) := by
  have hz := (groupCohomology.mem_cocycles₂_iff z.1).1 z.2
  have h1 := hz (g * x * g⁻¹) (g * y * g⁻¹) g
  have h2 := hz (g * x * g⁻¹) g y
  have h3 := hz g x y
  have e1 : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  have e2 : g * y * g⁻¹ * g = g * y := by group
  have e3 : g * x * g⁻¹ * g = g * x := by group
  rw [e1, e2] at h1
  rw [e3] at h2
  have hA : ∀ w, A.ρ g⁻¹ (A.ρ (g * x * g⁻¹) w) = A.ρ x (A.ρ g⁻¹ w) := by
    intro w
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have hB : ∀ w, A.ρ g⁻¹ (A.ρ g w) = w := by
    intro w
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have h1' := congrArg (A.ρ g⁻¹) h1
  have h2' := congrArg (A.ρ g⁻¹) h2
  have h3' := congrArg (A.ρ g⁻¹) h3
  simp only [map_add, map_sub, hA, hB] at h1' h2' h3' ⊢
  linear_combination (norm := module) h1' - h2' + h3'


/-- Conjugation as a monoid hom. -/
abbrev innerConjHom : G →* G := (MulAut.conj g).toMonoidHom

theorem innerConj_hT (x : G) (v : A) :
    (A.ρ g⁻¹) (A.ρ (innerConjHom g x) v) = A.ρ x ((A.ρ g⁻¹) v) := by
  change A.ρ g⁻¹ (A.ρ (g * x * g⁻¹) v) = _
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- Inner automorphisms act trivially on `H²`. -/
theorem h2Map_conj_self (y : groupCohomology.H2 A) :
    EdgeNat.h2Map (innerConjHom g) A A (A.ρ g⁻¹) (innerConj_hT A g) y = y := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective A y
  rw [EdgeNat.h2Map_π, groupCohomology.H2π_eq_iff]
  refine ⟨fun x => A.ρ g⁻¹ (z.1 (g * x * g⁻¹, g) - z.1 (g, x)), ?_⟩
  ext ⟨x, y⟩
  have := inner_conj_key A g z x y
  rw [groupCohomology.d₁₂_hom_apply]
  change _ = (groupCohomology.cochainsMap₂ (innerConjHom g) (EdgeNat.comparison (innerConjHom g) A A (A.ρ g⁻¹) (innerConj_hT A g)) z.1 - z.1) (x, y)
  exact this.symm

end TernaryPeriodPolynomials.Argument.GammaNStokes
