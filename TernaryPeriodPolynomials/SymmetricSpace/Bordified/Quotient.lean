module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingAction
public import TernaryPeriodPolynomials.SymmetricSpace.Rational.LocalCompact
public import TernaryPeriodPolynomials.SymmetricSpace.Corner.Separation
public import TernaryPeriodPolynomials.SymmetricSpace.CompactQuotient
public import TernaryPeriodPolynomials.SymmetricSpace.CoveringGeneral

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBordifiedQuotient
open Topology SymmetricSpacePositive SymmetricSpaceArithmeticProper SymmetricSpaceFlagCoordinates
  SymmetricSpaceRationalGluing

variable (H : Subgroup IntegralGL)

/-- The literal orbit space of the actual integral subgroup acting on the full rational gluing. -/
abbrev QuotientSpace := Quotient (MulAction.orbitRel H Glued)

def projection : Glued → QuotientSpace H := Quotient.mk _

theorem projection_openQuotient : IsOpenQuotientMap (projection H) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem projection_continuous : Continuous (projection H) := (projection_openQuotient H).continuous

theorem projection_smul (h : H) (x : Glued) : projection H (h • x) = projection H x :=
  Quotient.sound ⟨h,rfl⟩

/-- The actual dense family of interior arithmetic orbits. -/
def interiorProjection : Space → QuotientSpace H := projection H ∘ embedding

theorem interiorProjection_continuous : Continuous (interiorProjection H) :=
  (projection_continuous H).comp continuous_embedding

theorem interiorProjection_dense : DenseRange (interiorProjection H) :=
  (projection_openQuotient H).surjective.denseRange.comp embedding_denseRange
    (projection_continuous H)

/-- Literal translated corner maps into the arithmetic orbit quotient. -/
def translatedCorner (g : IntegralGL) : Corner → QuotientSpace H :=
  projection H ∘ integralAction g ∘ chart 1

theorem translatedCorner_continuous (g : IntegralGL) : Continuous (translatedCorner H g) :=
  (projection_continuous H).comp ((continuous_leftAction _).comp (continuous_chart 1))

theorem translatedCorner_embedding (g : IntegralGL) (S : Space) :
    translatedCorner H g (cornerEmbedding S) = interiorProjection H (act (realIntegral g) S) := by
  have he : chart 1 (cornerEmbedding S) = embedding S := by
    change chart 1 (cornerEmbedding S) = chart 1 (SymmetricSpaceRationalCharts.chartEmbedding 1 S)
    rw [SymmetricSpaceRationalCharts.chartEmbedding_apply]
    simp
  change projection H (integralAction g (chart 1 (cornerEmbedding S))) = _
  rw [he,integralAction_embedding]
  rfl

theorem interiorProjection_invariant (h : H) (S : Space) :
    interiorProjection H (act (realIntegral h.val) S) = interiorProjection H S := by
  change projection H (embedding (act (realIntegral h.val) S)) = projection H (embedding S)
  exact (congrArg (projection H) (integralAction_embedding h.val S)).symm.trans
    (projection_smul H h (embedding S))

instance quotientLocallyCompact : LocallyCompactSpace (QuotientSpace H) :=
  (projection_openQuotient H).locallyCompactSpace

instance quotientSecondCountable : SecondCountableTopology (QuotientSpace H) :=
  (projection_openQuotient H).secondCountableTopology

/-- Exact compactness consequence for the actual finite-index orbit space. The Hausdorff premise follows from the separate arithmetic properness theorem. -/
theorem compact_of_hausdorff [H.FiniteIndex] [T2Space (QuotientSpace H)] :
    CompactSpace (QuotientSpace H) :=
  SymmetricSpaceCompactQuotient.compact_of_finite_index_invariant H
    (interiorProjection H) (interiorProjection_dense H)
    (translatedCorner H) (translatedCorner_continuous H)
    (translatedCorner_embedding H) (interiorProjection_invariant H)

/-- Actual properness implies Hausdorffness; it is not inferred just from compact representatives. -/
theorem hausdorff_of_finite_transporters
    (hfinite : ∀ C D : Set Glued, IsCompact C → IsCompact D →
      {h : H | ((h • ·) '' C ∩ D).Nonempty}.Finite) : T2Space (QuotientSpace H) :=
  SymmetricSpaceCovering.quotient_t2_of_finite_transporters hfinite

end TernaryPoly.SymmetricSpaceBordifiedQuotient
