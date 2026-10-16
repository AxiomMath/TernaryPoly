module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallCover
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityCoverHomeomorph

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set
open SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open SingularLocalCompactDuality

/-- The actual coordinate covering is the genuine positive trace-one matrix space. -/
def coordinateCoverHomeomorph : CoverOpen univ ≃ₜ Space :=
  (Homeomorph.setCongr liftedDomain_univ).trans chartHomeomorph.symm

/-- The homeomorphism is literal reconstruction by the existing coordinate chart. -/
theorem coordinateCoverHomeomorph_apply (x : CoverOpen univ) :
    coordinateCoverHomeomorph x = coordinateChart.symm x.val := by
  apply Subtype.ext
  exact (coordinateChart_inverse x.val x.property.1).symm

/-- The genuine matrix/coordinate homeomorphism is equivariant for the actual deck action. -/
theorem coordinateCoverHomeomorph_equivariant (g : DeckGroup) (x : CoverOpen univ) :
    coordinateCoverHomeomorph (g • x) = g • coordinateCoverHomeomorph x := by
  rw [coordinateCoverHomeomorph_apply, coordinateCoverHomeomorph_apply]
  exact deckMap_inverseChart g x.property.1

/-- The actual original matrix-space quotient projection as a continuous categorical map. -/
def matrixQuotientProjection : TopCat.of Space ⟶ TopCat.of OrbitSpace :=
  TopCat.ofHom ⟨quotientProjection, quotientProjection_covering.continuous⟩

/-- Coordinates retain the actual quotient projection pointwise. -/
theorem coordinateCover_projection (x : CoverOpen univ) :
    matrixQuotientProjection (coordinateCoverHomeomorph x) = coverProjection univ x := by
  rw [coordinateCoverHomeomorph_apply]
  rfl

/-- The genuine global coordinate projection is an actual quotient covering. -/
theorem coordinateCover_quotientCovering : IsQuotientCoveringMap (coverProjection univ) DeckGroup := by
  have he : (coverProjection univ : CoverOpen univ → OrbitSpace) = quotientProjection ∘ coordinateCoverHomeomorph :=
    funext (fun x => (coordinateCover_projection x).symm)
  apply (isQuotientCoveringMap_iff_isCoveringMap_and _ _).mpr
  refine ⟨?_, ?_, inferInstance, inferInstance, ?_⟩
  · rw [he]
    exact quotientProjection_covering.comp_homeomorph coordinateCoverHomeomorph
  · rw [he]
    exact quotientProjection_surjective.comp coordinateCoverHomeomorph.surjective
  · intro x y
    constructor
    · intro h
      have hq : quotientProjection (coordinateCoverHomeomorph x) = quotientProjection (coordinateCoverHomeomorph y) :=
        (coordinateCover_projection x).trans (h.trans (coordinateCover_projection y).symm)
      obtain ⟨g, hg⟩ := quotientProjection_quotientCovering.apply_eq_iff_mem_orbit.mp hq
      exact ⟨g, coordinateCoverHomeomorph.injective ((coordinateCoverHomeomorph_equivariant g y).trans hg)⟩
    · rintro ⟨g, rfl⟩
      exact coverProjection_deck univ g y

instance coordinateCoverFact : Fact (IsQuotientCoveringMap (coverProjection univ) DeckGroup) :=
  ⟨coordinateCover_quotientCovering⟩

instance matrixQuotientCoverFact : Fact (IsQuotientCoveringMap matrixQuotientProjection DeckGroup) :=
  ⟨quotientProjection_quotientCovering⟩

/-- A literal equivariant covering-homeomorphism square connects the new coordinates to the
genuine positive matrix quotient, with the identity on the quotient base. -/
def coordinateMatrixCoverHomeomorph : CoverHomeomorph (G := DeckGroup)
    (coverProjection univ) matrixQuotientProjection where
  total := coordinateCoverHomeomorph
  base := Homeomorph.refl _
  square := by ext x; exact coordinateCover_projection x
  equivariant := coordinateCoverHomeomorph_equivariant

end TernaryPoly.SmoothSingularGlobal
