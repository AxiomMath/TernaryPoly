module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.SpaceComparison
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Embeddings
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionGeometry
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Cohomology

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory HomologicalComplex FreeActionLinearization CoveringSingularOrbits
open SymmetricSpaceRationalGluing SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence
open scoped Classical

/-- Genuine geometric chains on the entire actual arithmetic boundary, including every corner stratum. -/
abbrev boundaryLocalChains (V : Rep.{0} ℚ principalSix) : ChainComplex (ModuleCat ℚ) ℕ :=
  localChains SingularBoundaryRestriction.boundaryProjection
    SingularBoundaryRestriction.boundaryQuotientCovering V

/-- The actual full-boundary inclusion on genuine geometric local-coefficient chains. -/
def boundaryInclusionMap (V : Rep.{0} ℚ principalSix) : boundaryLocalChains V ⟶ bordifiedLocalChains V :=
  localSpaceMap SingularBoundaryRestriction.boundaryInclusion
    SingularBoundaryRestriction.boundaryInclusion_equivariant V
    SingularBoundaryRestriction.boundaryProjection bordifiedProjection
    SingularBoundaryRestriction.boundaryQuotientCovering bordifiedProjection_quotientCovering

/-- The entire boundary inclusion sends each actual simplex and coefficient to its literal image. -/
theorem boundaryInclusionMap_single (V : Rep.{0} ℚ principalSix) (n : ℕ)
    (σ : SingularSimplex (TopCat.of SingularBoundaryRestriction.BoundaryBase) n)
    (c : FiberCoefficient SingularBoundaryRestriction.boundaryProjection
      SingularBoundaryRestriction.boundaryQuotientCovering V (atVertex σ)) :
    (boundaryInclusionMap V).f n (DFinsupp.single σ c) =
      DFinsupp.single (projection SingularBoundaryRestriction.boundaryBaseInclusion n σ)
        (coefficientPushforward SingularBoundaryRestriction.boundaryProjection bordifiedProjection
          SingularBoundaryRestriction.boundaryInclusion SingularBoundaryRestriction.boundaryBaseInclusion
          SingularBoundaryRestriction.boundary_square SingularBoundaryRestriction.boundaryQuotientCovering
          bordifiedProjection_quotientCovering SingularBoundaryRestriction.boundaryInclusion_equivariant
          V (atVertex σ) c) :=
  localSpaceMap_single SingularBoundaryRestriction.boundaryInclusion
    SingularBoundaryRestriction.boundaryInclusion_equivariant V
    SingularBoundaryRestriction.boundaryProjection bordifiedProjection
    SingularBoundaryRestriction.boundaryBaseInclusion SingularBoundaryRestriction.boundary_square
    SingularBoundaryRestriction.boundaryQuotientCovering bordifiedProjection_quotientCovering n σ c

/-- The actual full-boundary inclusion is injective on every geometric local-chain degree. -/
theorem boundaryInclusionMap_injective (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    Function.Injective ((boundaryInclusionMap V).f n) :=
  localSpaceMap_injective SingularBoundaryRestriction.boundaryProjection bordifiedProjection
    SingularBoundaryRestriction.boundaryInclusion SingularBoundaryRestriction.boundaryBaseInclusion
    SingularBoundaryRestriction.boundary_square SingularBoundaryRestriction.boundaryQuotientCovering
    bordifiedProjection_quotientCovering SingularBoundaryRestriction.boundaryInclusion_equivariant
    V Subtype.val_injective n

/-- The genuine boundary chain map is a monomorphism in every degree. -/
instance boundaryInclusionMap_mono (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    Mono ((boundaryInclusionMap V).f n) :=
  (ModuleCat.mono_iff_injective _).mpr (boundaryInclusionMap_injective V n)

/-- Genuine geometric local-coefficient chains on the original arithmetic interior. -/
abbrev interiorLocalChains (V : Rep.{0} ℚ principalSix) : ChainComplex (ModuleCat ℚ) ℕ :=
  localChains SymmetricSpaceBordifiedCohomology.interiorCover
    SymmetricSpaceBordifiedCohomology.interiorCover_isQuotientCovering V

/-- The original arithmetic interior includes into the actual compact bordification on local chains. -/
def interiorInclusionMap (V : Rep.{0} ℚ principalSix) : interiorLocalChains V ⟶ bordifiedLocalChains V :=
  localSpaceMap SymmetricSpaceBordifiedCohomology.upstairs
    SymmetricSpaceBordifiedCohomology.upstairs_equivariant V
    SymmetricSpaceBordifiedCohomology.interiorCover bordifiedProjection
    SymmetricSpaceBordifiedCohomology.interiorCover_isQuotientCovering bordifiedProjection_quotientCovering

/-- Actual interior local-coefficient homology equals group homology in every degree. -/
def interiorGroupLocalHomologyIso (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    groupHomology V n ≅ (interiorLocalChains V).homology n :=
  groupLocalHomologyIso SymmetricSpaceBordifiedCohomology.interiorCover
    SymmetricSpaceBordifiedCohomology.interiorCover_isQuotientCovering V n

/-- The actual interior inclusion is the identity on group homology under the genuine comparisons. -/
theorem interiorInclusion_group_comparison (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    (interiorGroupLocalHomologyIso V n).hom ≫ homologyMap (interiorInclusionMap V) n =
      (bordifiedGroupLocalHomologyIso V n).hom :=
  groupLocalHomologyIso_space_natural SymmetricSpaceBordifiedCohomology.upstairs
    SymmetricSpaceBordifiedCohomology.upstairs_equivariant
    SymmetricSpaceBordifiedCohomology.interiorCover bordifiedProjection
    SymmetricSpaceBordifiedCohomology.interiorCover_isQuotientCovering bordifiedProjection_quotientCovering V n

/-- The actual arithmetic interior inclusion induces an isomorphism in every local-homology degree. -/
instance interiorInclusion_homology_isIso (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    IsIso (homologyMap (interiorInclusionMap V) n) :=
  localSpaceMap_homology_isIso SymmetricSpaceBordifiedCohomology.upstairs
    SymmetricSpaceBordifiedCohomology.upstairs_equivariant
    SymmetricSpaceBordifiedCohomology.interiorCover bordifiedProjection
    SymmetricSpaceBordifiedCohomology.interiorCover_isQuotientCovering bordifiedProjection_quotientCovering V n

end TernaryPoly.SingularLocalHomology
