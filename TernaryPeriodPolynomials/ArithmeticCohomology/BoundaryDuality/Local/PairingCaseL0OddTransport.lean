module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneQuot

@[expose] public section


/-!
# Transport of crossed cohomology along a group endomorphism and an intertwiner

Let `ρ` be a representation of a group `G` on `V`, `a : G →* G` an endomorphism and `E : V → V` a
linear map with `E (ρ (a γ) v) = ρ γ (E v)`.  Then `c ↦ (γ ↦ E (c (a γ)))` maps crossed cocycles
to crossed cocycles and crossed coboundaries to crossed coboundaries, hence induces a linear
endomorphism `transportH1` of `H¹(G, ρ)`.

If `E` is bijective and `a` is surjective then `transportH1` is injective, and an injective
endomorphism of a finite-dimensional space that preserves a submodule is onto that submodule if
it is injective there (`transportH1_surjective_on`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTransport

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  (a : G →* G) (E : V →ₗ[ℂ] V) (hE : ∀ γ v, E (ρ (a γ) v) = ρ γ (E v))

/-- **The transported cocycle** `γ ↦ E (c (a γ))`. -/
def transportCocycles : crossedCocycles ρ →ₗ[ℂ] crossedCocycles ρ where
  toFun c := ⟨fun γ => E (c.1 (a γ)), by
    intro g h
    change E (c.1 (a (g * h))) = E (c.1 (a g)) + ρ g (E (c.1 (a h)))
    rw [map_mul, c.2 (a g) (a h), map_add, hE]⟩
  map_add' c d := Subtype.ext (funext fun γ => map_add E (c.1 (a γ)) (d.1 (a γ)))
  map_smul' r c := Subtype.ext (funext fun γ => map_smul E r (c.1 (a γ)))

theorem transportCocycles_apply (c : crossedCocycles ρ) (γ : G) :
    (transportCocycles ρ a E hE c).1 γ = E (c.1 (a γ)) := rfl

theorem transportCocycles_boundary (v : V) :
    transportCocycles ρ a E hE (crossedBoundary ρ v) = crossedBoundary ρ (E v) := by
  apply Subtype.ext
  funext γ
  change E (ρ (a γ) v - v) = ρ γ (E v) - E v
  rw [map_sub, hE]

theorem transportCocycles_boundaries :
    crossedBoundaries ρ ≤ (crossedBoundaries ρ).comap (transportCocycles ρ a E hE) := by
  rintro c ⟨v, rfl⟩
  exact ⟨E v, (transportCocycles_boundary ρ a E hE v).symm⟩

/-- **The transport on `H¹(G, ρ)`**: `[c] ↦ [γ ↦ E (c (a γ))]`. -/
def transportH1 : CrossedH1 ρ →ₗ[ℂ] CrossedH1 ρ :=
  (crossedBoundaries ρ).mapQ (crossedBoundaries ρ) (transportCocycles ρ a E hE)
    (transportCocycles_boundaries ρ a E hE)

theorem transportH1_qcls (c : crossedCocycles ρ) :
    transportH1 ρ a E hE (qcls ρ c) = qcls ρ (transportCocycles ρ a E hE c) := rfl

/-- **Injectivity of the transport** for a bijective intertwiner and a surjective endomorphism. -/
theorem transportH1_injective (hEinj : Function.Injective E) (hEsurj : Function.Surjective E)
    (ha : Function.Surjective a) : Function.Injective (transportH1 ρ a E hE) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  change transportH1 ρ a E hE (qcls ρ c) = 0 at hx
  rw [transportH1_qcls, qcls_eq_zero_iff] at hx
  obtain ⟨u, hu⟩ := hx
  obtain ⟨u', rfl⟩ := hEsurj u
  change qcls ρ c = 0
  rw [qcls_eq_zero_iff]
  refine ⟨u', ?_⟩
  apply Subtype.ext
  funext δ
  obtain ⟨γ, rfl⟩ := ha δ
  have h1 := congrArg (fun z : crossedCocycles ρ => z.1 γ) hu
  change ρ γ (E u') - E u' = E (c.1 (a γ)) at h1
  rw [← hE] at h1
  have h2 : E (ρ (a γ) u' - u') = E (c.1 (a γ)) := by rw [map_sub, h1]
  exact hEinj h2

/-- **A transport that preserves a finite-dimensional submodule is onto it** when it is
injective. -/
theorem transportH1_surjective_on (hinj : Function.Injective (transportH1 ρ a E hE))
    (P : Submodule ℂ (CrossedH1 ρ)) [FiniteDimensional ℂ P]
    (hP : ∀ x ∈ P, transportH1 ρ a E hE x ∈ P) :
    ∀ w ∈ P, ∃ y ∈ P, transportH1 ρ a E hE y = w := by
  let f : P →ₗ[ℂ] P := (transportH1 ρ a E hE).restrict hP
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact hinj (congrArg Subtype.val h)
  have hs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf
  intro w hw
  obtain ⟨y, hy⟩ := hs ⟨w, hw⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTransport

end
