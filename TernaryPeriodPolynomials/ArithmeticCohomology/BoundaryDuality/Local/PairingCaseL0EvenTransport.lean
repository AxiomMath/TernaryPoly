module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LeviCrossedAction

@[expose] public section


/-!
# Transport of crossed homomorphisms along a multiplicative map and an equivariant linear map

Let `a : G → G` be multiplicative and `E : V₁ → V₂` linear with `E (ρ₁ (a g) v) = ρ₂ g (E v)`.  A
crossed homomorphism `x` of `ρ₁` gives the crossed homomorphism `g ↦ - E (x (a g))` of `ρ₂`
(`transportCocycles`); coboundaries go to coboundaries, so the transport acts on the crossed `H¹`
(`transportH1`), and for an involution `a` and a two-sided inverse `E'` of `E` the two transports
are inverse (`transportCocycles_transportCocycles`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

section Transport

variable {G V₁ V₂ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
  [Module ℂ V₂]

/-- **Transport of crossed homomorphisms.**  Along a multiplicative `a : G → G` and a linear map `E`
with `E (ρ₁ (a g) v) = ρ₂ g (E v)`, a crossed homomorphism `x` of `ρ₁` gives the crossed
homomorphism `g ↦ - E (x (a g))` of `ρ₂`. -/
def transportCocycles (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (a : G → G)
    (ha : ∀ g h, a (g * h) = a g * a h) (E : V₁ →ₗ[ℂ] V₂)
    (hE : ∀ g v, E (ρ₁ (a g) v) = ρ₂ g (E v)) :
    crossedCocycles ρ₁ →ₗ[ℂ] crossedCocycles ρ₂ where
  toFun x := ⟨fun g => -E (x.1 (a g)), by
    intro g h
    change -E (x.1 (a (g * h))) = -E (x.1 (a g)) + ρ₂ g (-E (x.1 (a h)))
    rw [ha, x.2 (a g) (a h)]
    simp only [map_add, map_neg, hE, neg_add]⟩
  map_add' x y := by
    apply Subtype.ext
    funext g
    change -E (x.1 (a g) + y.1 (a g)) = -E (x.1 (a g)) + -E (y.1 (a g))
    rw [map_add, neg_add]
  map_smul' r x := by
    apply Subtype.ext
    funext g
    change -E (r • x.1 (a g)) = r • -E (x.1 (a g))
    rw [map_smul, smul_neg]

/-- The values of the transport. -/
theorem transportCocycles_apply (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    (a : G → G) (ha : ∀ g h, a (g * h) = a g * a h) (E : V₁ →ₗ[ℂ] V₂)
    (hE : ∀ g v, E (ρ₁ (a g) v) = ρ₂ g (E v)) (x : crossedCocycles ρ₁) (g : G) :
    (transportCocycles ρ₁ ρ₂ a ha E hE x).1 g = -E (x.1 (a g)) := rfl

/-- The transport of a coboundary is a coboundary. -/
theorem transportCocycles_boundary (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    (a : G → G) (ha : ∀ g h, a (g * h) = a g * a h) (E : V₁ →ₗ[ℂ] V₂)
    (hE : ∀ g v, E (ρ₁ (a g) v) = ρ₂ g (E v)) (u : V₁) :
    transportCocycles ρ₁ ρ₂ a ha E hE (crossedBoundary ρ₁ u) = crossedBoundary ρ₂ (-E u) := by
  apply Subtype.ext
  funext g
  change -E (ρ₁ (a g) u - u) = ρ₂ g (-E u) - -E u
  simp only [map_sub, map_neg, hE]
  abel

/-- **The transport on crossed `H¹`.** -/
def transportH1 (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (a : G → G)
    (ha : ∀ g h, a (g * h) = a g * a h) (E : V₁ →ₗ[ℂ] V₂)
    (hE : ∀ g v, E (ρ₁ (a g) v) = ρ₂ g (E v)) : CrossedH1 ρ₁ →ₗ[ℂ] CrossedH1 ρ₂ :=
  (crossedBoundaries ρ₁).mapQ (crossedBoundaries ρ₂) (transportCocycles ρ₁ ρ₂ a ha E hE) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨-E u, (transportCocycles_boundary ρ₁ ρ₂ a ha E hE u).symm⟩)

/-- The transport on classes of crossed homomorphisms. -/
theorem transportH1_mk (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (a : G → G)
    (ha : ∀ g h, a (g * h) = a g * a h) (E : V₁ →ₗ[ℂ] V₂)
    (hE : ∀ g v, E (ρ₁ (a g) v) = ρ₂ g (E v)) (x : crossedCocycles ρ₁) :
    transportH1 ρ₁ ρ₂ a ha E hE ((crossedBoundaries ρ₁).mkQ x) =
      (crossedBoundaries ρ₂).mkQ (transportCocycles ρ₁ ρ₂ a ha E hE x) := rfl

/-- **The transport along an involution and an inverse isomorphism is inverse.** -/
theorem transportCocycles_transportCocycles (ρ₁ : Representation ℂ G V₁)
    (ρ₂ : Representation ℂ G V₂) (a : G → G) (ha : ∀ g h, a (g * h) = a g * a h)
    (haa : ∀ g, a (a g) = g) (E : V₁ →ₗ[ℂ] V₂) (E' : V₂ →ₗ[ℂ] V₁)
    (hE : ∀ g v, E (ρ₁ (a g) v) = ρ₂ g (E v)) (hE' : ∀ g w, E' (ρ₂ (a g) w) = ρ₁ g (E' w))
    (hEE' : ∀ v, E' (E v) = v) (x : crossedCocycles ρ₁) :
    transportCocycles ρ₂ ρ₁ a ha E' hE' (transportCocycles ρ₁ ρ₂ a ha E hE x) = x := by
  apply Subtype.ext
  funext g
  change -E' (-E (x.1 (a (a g)))) = x.1 g
  rw [haa, map_neg, neg_neg, hEE']

end Transport

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
