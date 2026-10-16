module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryForget
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Cohomology
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionRelative

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCoefficient SingularCoverNaturality EquivariantSingularSmall
open SingularLocalCompactDuality SingularBoundaryRestriction
open SymmetricSpacePositive SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence SymmetricSpaceBordifiedCohomology

/-- The genuine whole compact-bordification projection retains its quotient-covering fact. -/
instance wholeCoverFact : Fact (IsQuotientCoveringMap wholeProjection principalSix) :=
  ⟨wholeQuotientCovering⟩

/-- The genuine original arithmetic interior projection retains its quotient-covering fact. -/
instance interiorCoverFact : Fact (IsQuotientCoveringMap interiorCover principalSix) :=
  ⟨interiorCover_isQuotientCovering⟩

/-- The already-proved actual bordification is Hausdorff. -/
instance bordifiedT2 : T2Space BordifiedOrbit :=
  SymmetricSpaceCompactBordification.actual_compact_bordification.1

/-- The already-proved actual bordification is compact. -/
instance bordifiedCompact : CompactSpace BordifiedOrbit :=
  SymmetricSpaceCompactBordification.actual_compact_bordification.2.1

/-- The designated actual open interior, with the original orbit-embedding image. -/
def interiorOpen : Opens (TopCat.of BordifiedOrbit) :=
  ⟨Set.range (interiorEmbedding principalSix),(interiorEmbedding_isOpenEmbedding principalSix).isOpen_range⟩

/-- The designated open interior is exactly the complement of the actual boundary. -/
theorem interiorOpen_compl : (interiorOpen : Set BordifiedOrbit)ᶜ = boundary principalSix := rfl

/-- Every actual covering preimage is invariant under the genuine principal-six action. -/
instance wholePreimageInvariant (W : Set BordifiedOrbit) :
    Fact (InvariantSet principalSix (TopCat.of Glued) (wholeProjection ⁻¹' W)) :=
  ⟨preimage_invariant (G := principalSix) wholeProjection W⟩

/-- The canonical preimage action on each actual restriction of the whole covering. -/
instance wholePreimageAction (W : Set BordifiedOrbit) : MulAction principalSix (wholeProjection ⁻¹' W) :=
  EquivariantSingularSmall.invariantSubtypeAction principalSix (TopCat.of Glued) _

/-- The canonical preimage action is continuous on every actual restricted cover. -/
instance wholePreimageContinuous (W : Set BordifiedOrbit) :
    ContinuousConstSMul principalSix (wholeProjection ⁻¹' W) :=
  EquivariantSingularSmall.invariantSubtypeContinuous principalSix (TopCat.of Glued) _

/-- Each actual restriction retains its genuine quotient-covering fact. -/
instance wholeRestrictedCoverFact (W : Set BordifiedOrbit) :
    Fact (IsQuotientCoveringMap (restrictedProjection wholeProjection W) principalSix) :=
  ⟨restrictedQuotientCovering (G := principalSix) wholeProjection W⟩

/-- The original arithmetic interior covering and the actual restricted whole covering
are related by the literal upstairs/downstairs inclusion homeomorphisms. -/
def interiorCoverHomeomorph : CoverHomeomorph (G := principalSix)
    interiorCover (restrictedProjection wholeProjection interiorOpen) where
  total := embedding_isOpenEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (projection_preimage_interior principalSix).symm)
  base := (interiorEmbedding_isOpenEmbedding principalSix).isEmbedding.toHomeomorph
  square := by ext x; rfl
  equivariant g x := Subtype.ext (embedding_equivariant principalSix g x)

/-- The actual interior homeomorphism has the original symmetric-space embedding upstairs. -/
theorem interiorCoverHomeomorph_total (x : Space) :
    (interiorCoverHomeomorph.total x).val = embedding x := rfl

/-- The actual base homeomorphism has the original interior orbit inclusion downstairs. -/
theorem interiorCoverHomeomorph_base (x : InteriorOrbit principalSix) :
    (interiorCoverHomeomorph.base x).val = interiorEmbedding principalSix x := rfl

/-- Genuine restriction to the open interior followed by the actual cover-homeomorphism
pullback is exactly the original interior restriction. -/
theorem interiorRestriction_square (V : Rep.{0} ℚ principalSix) :
    localRestriction wholeProjection interiorOpen V ≫ coveringCochainMap interiorCoverHomeomorph V =
      interiorRestriction V := by
  unfold localRestriction coveringCochainMap
  erw [← localPullback_comp]
  rfl

/-- The actual compact cohomology of the original interior agrees with that of the open
restriction through the genuine covering homeomorphism. -/
def interiorCompactIso (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    compactCohomology interiorCover V k ≅
      compactCohomology (restrictedProjection wholeProjection interiorOpen) V k :=
  (coveringCompactIso interiorCoverHomeomorph V k).symm

/-- The actual interior compact-cohomology comparison preserves literal support-forgetting. -/
theorem interiorCompactIso_forget (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    (interiorCompactIso V k).hom ≫ compactForget (restrictedProjection wholeProjection interiorOpen) V k ≫
      homologyMap (coveringCochainMap interiorCoverHomeomorph V) k = compactForget interiorCover V k := by
  rw [← coveringCompactIso_forget interiorCover V _ interiorCoverHomeomorph k]
  exact Iso.inv_hom_id_assoc _ _

end TernaryPoly.CompactInteriorRelativeBoundary
