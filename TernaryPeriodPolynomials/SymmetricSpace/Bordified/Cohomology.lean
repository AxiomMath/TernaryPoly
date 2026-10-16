module

public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Contractible
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityComparison
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.SymmetricSpaceArithmeticProperConsumer

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBordifiedCohomology
open CategoryTheory HomologicalComplex Topology
open SymmetricSpacePositive SymmetricSpaceRationalGluing SymmetricSpaceArithmeticProper
  SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence
  SingularLocalCoefficient SingularCoverNaturality

instance interiorContinuous : ContinuousConstSMul principalSix Space where
  continuous_const_smul g := continuous_act (realIntegral g.val)

instance interiorFree : IsCancelSMul principalSix Space :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr principalSix_subgroup_fixed_eq_one

instance bordifiedFree : IsCancelSMul principalSix Glued :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr SymmetricSpaceCompactBordification.principalSix_free

/-- The actual interior covering, with the same literal principal-six deck group as the boundary. -/
def interiorCover : TopCat.of Space ⟶ TopCat.of (InteriorOrbit principalSix) :=
  TopCat.ofHom ⟨Quotient.mk _,continuous_quotient_mk'⟩

/-- The actual compact bordification covering as a continuous map. -/
def bordifiedCover : TopCat.of Glued ⟶ TopCat.of BordifiedOrbit :=
  TopCat.ofHom ⟨projection principalSix,projection_continuous principalSix⟩

theorem interiorCover_isQuotientCovering : IsQuotientCoveringMap interiorCover principalSix := by
  apply SymmetricSpaceCovering.quotientCovering_of_finite_transporters
  · intro C D hC hD
    apply Set.Finite.of_finite_image (f := principalSix.subtype)
    · apply (SymmetricSpaceArithmeticProper.compact_transporter_finite C D hC hD).subset
      rintro _ ⟨g,hg,rfl⟩
      obtain ⟨_,⟨S,hS,rfl⟩,hT⟩ := hg
      exact ⟨S,hS,hT⟩
    · exact Subtype.val_injective.injOn
  · exact principalSix_subgroup_fixed_eq_one

/-- The full rational gluing is the actual free contractible cover of the bordified quotient. -/
theorem bordifiedCover_quotientCovering : IsQuotientCoveringMap bordifiedCover principalSix :=
  SymmetricSpaceCovering.quotientCovering_of_finite_transporters
    (SymmetricSpaceCompactBordification.subgroup_compact_transporters principalSix)
    SymmetricSpaceCompactBordification.principalSix_free

/-- The actual inclusion upstairs and its actual quotient map downstairs. -/
def upstairs : TopCat.of Space ⟶ TopCat.of Glued := TopCat.ofHom ⟨embedding,continuous_embedding⟩

def downstairs : TopCat.of (InteriorOrbit principalSix) ⟶ TopCat.of BordifiedOrbit :=
  TopCat.ofHom ⟨interiorEmbedding principalSix,
    (interiorEmbedding_isOpenEmbedding principalSix).continuous⟩

theorem inclusion_square : upstairs ≫ bordifiedCover = interiorCover ≫ downstairs := rfl

theorem upstairs_equivariant (g : principalSix) (S : Space) :
    upstairs (g • S)=g • upstairs S := embedding_equivariant principalSix g S

/-- Actual fiber-valued singular cochains on the compact bordification. -/
abbrev bordifiedLocalCochains (V : Rep.{0} ℚ principalSix) :=
  localCochains bordifiedCover bordifiedCover_quotientCovering V

/-- Actual fiber-valued singular cochains on its original arithmetic interior. -/
abbrev interiorLocalCochains (V : Rep.{0} ℚ principalSix) :=
  localCochains interiorCover interiorCover_isQuotientCovering V

/-- Literal local-system restriction through the actual inclusion square. -/
def interiorRestriction (V : Rep.{0} ℚ principalSix) :
    bordifiedLocalCochains V ⟶ interiorLocalCochains V :=
  localPullback interiorCover bordifiedCover upstairs downstairs inclusion_square
    interiorCover_isQuotientCovering bordifiedCover_quotientCovering upstairs_equivariant V

/-- Genuine group cohomology equals genuine singular local-system cohomology of the compact
bordification, in every degree and for arbitrary rational coefficient representations. -/
def groupBordifiedCohomologyIso (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    groupCohomology V n ≅ (bordifiedLocalCochains V).homology n :=
  groupLocalCohomologyIso bordifiedCover bordifiedCover_quotientCovering V n

def groupInteriorCohomologyIso (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    groupCohomology V n ≅ (interiorLocalCochains V).homology n :=
  groupLocalCohomologyIso interiorCover interiorCover_isQuotientCovering V n

/-- The actual restriction to the interior is the identity on group cohomology under comparison. -/
theorem groupBordifiedCohomologyIso_restriction (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    (groupBordifiedCohomologyIso V n).hom ≫ homologyMap (interiorRestriction V) n =
      (groupInteriorCohomologyIso V n).hom :=
  groupLocalCohomologyIso_pullback interiorCover bordifiedCover upstairs downstairs inclusion_square
    interiorCover_isQuotientCovering bordifiedCover_quotientCovering upstairs_equivariant V n

/-- The actual arithmetic-interior inclusion induces an isomorphism on all local cohomology. -/
instance interiorRestriction_isIso (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    IsIso (homologyMap (interiorRestriction V) n) :=
  localPullback_homology_isIso interiorCover bordifiedCover upstairs downstairs inclusion_square
    interiorCover_isQuotientCovering bordifiedCover_quotientCovering upstairs_equivariant V n

end TernaryPoly.SymmetricSpaceBordifiedCohomology
