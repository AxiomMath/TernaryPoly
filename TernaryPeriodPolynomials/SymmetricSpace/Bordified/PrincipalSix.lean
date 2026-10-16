module

public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Interior
public import TernaryPeriodPolynomials.SymmetricSpace.Covering
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
open Topology SymmetricSpacePositive IntegralGL3Congruence SymmetricSpaceCovering
  SymmetricSpaceBordifiedQuotient SymmetricSpaceArithmeticProper

/-- The two literal presentations of the level-six group have exactly the same orbits. -/
theorem orbit_relation_iff (x y : Space) :
    MulAction.orbitRel DeckGroup Space x y ↔ MulAction.orbitRel principalSix Space x y := by
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨⟨g.val.val,g.property⟩,hg⟩
  · rintro ⟨g,hg⟩
    exact ⟨⟨⟨g.val,principalSix_le_K g.property⟩,g.property⟩,hg⟩

/-- The already-constructed arithmetic manifold is the literal interior orbit space,
via the identity on positive matrices. -/
def arithmeticInteriorHomeomorph : OrbitSpace ≃ₜ InteriorOrbit principalSix :=
  Homeomorph.Quotient.congrRight orbit_relation_iff

@[simp] theorem arithmeticInteriorHomeomorph_mk (S : Space) :
    arithmeticInteriorHomeomorph (quotientProjection S) = Quotient.mk _ S := rfl

/-- The actual bordified arithmetic orbit space for the exact principal-six cover. -/
abbrev BordifiedOrbit := QuotientSpace principalSix

def arithmeticEmbedding : OrbitSpace → BordifiedOrbit :=
  interiorEmbedding principalSix ∘ arithmeticInteriorHomeomorph

@[simp] theorem arithmeticEmbedding_projection (S : Space) :
    arithmeticEmbedding (quotientProjection S) = interiorProjection principalSix S := rfl

theorem arithmeticEmbedding_isOpenEmbedding : IsOpenEmbedding arithmeticEmbedding :=
  (interiorEmbedding_isOpenEmbedding principalSix).comp arithmeticInteriorHomeomorph.isOpenEmbedding

theorem arithmeticEmbedding_dense : DenseRange arithmeticEmbedding :=
  (interiorEmbedding_dense principalSix).comp arithmeticInteriorHomeomorph.surjective.denseRange
    (interiorEmbedding_isOpenEmbedding principalSix).continuous

/-- This is the precise outstanding compactness gate for the actual principal-six quotient. -/
theorem compact_of_hausdorff [T2Space BordifiedOrbit] : CompactSpace BordifiedOrbit :=
  SymmetricSpaceBordifiedQuotient.compact_of_hausdorff principalSix

end TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
