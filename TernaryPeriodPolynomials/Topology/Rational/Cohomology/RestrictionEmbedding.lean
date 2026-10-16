module

public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.Restriction

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalCohomologyRestriction
open CategoryTheory
variable {G H : Type} [Group G] [Group H]

/-- Restriction along an injective group homomorphism factors through its actual range,
followed by the isomorphism that parameterizes that subgroup. -/
def rangeCohomologyIso (f : H →* G) (hf : Function.Injective f) (A : Rep ℚ G) (n : ℕ) :
    groupCohomology (Rep.res f A) n ≅ groupCohomology (Rep.res f.range.subtype A) n :=
  groupCohomology.mapIso (MonoidHom.ofInjective hf) (LinearEquiv.refl ℚ A)
    (by intro h; rfl) n

theorem restriction_embedding_factor (f : H →* G) (hf : Function.Injective f)
    (A : Rep ℚ G) (n : ℕ) :
    groupCohomology.map f (𝟙 (Rep.res f A)) n =
      groupCohomology.map f.range.subtype (𝟙 (Rep.res f.range.subtype A)) n ≫
        (rangeCohomologyIso f hf A n).inv := by
  let ψ : Rep.res (MonoidHom.ofInjective hf).toMonoidHom (Rep.res f.range.subtype A) ⟶
      Rep.res f A := Rep.ofHom ⟨LinearMap.id,by intro h; rfl⟩
  exact groupCohomology.map_comp f.range.subtype (MonoidHom.ofInjective hf).toMonoidHom
    (𝟙 (Rep.res f.range.subtype A)) ψ n

/-- Actual cohomology restriction along any finite-index embedding is injective,
without assumptions on dimension or generation of its rational coefficient module. -/
theorem restriction_embedding_injective (f : H →* G) (hf : Function.Injective f)
    [f.range.FiniteIndex] (A : Rep ℚ G) (n : ℕ) :
    Function.Injective (groupCohomology.map f (𝟙 (Rep.res f A)) n) := by
  rw [restriction_embedding_factor f hf A n]
  intro x y hxy
  apply restriction_injective f.range A n
  have hh := congrArg (fun z => (rangeCohomologyIso f hf A n).hom z) hxy
  simpa using hh

end TernaryPoly.RationalCohomologyRestriction
