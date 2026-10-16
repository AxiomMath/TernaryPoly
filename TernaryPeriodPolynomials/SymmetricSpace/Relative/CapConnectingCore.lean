module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.CapConnectingGeometric
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionRelative
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Inclusions
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.OrientationClass

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeCapConnecting
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open SingularBoundaryRestriction SingularLocalCoefficient SingularLocalHomology SingularLocalCap
open SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix

/-- Cap against the actual relative fundamental class, on genuine geometric relative cohomology. -/
def relativeFundamentalCap (V : Rep.{0} ℚ principalSix) :
    (geometricRelativeCochains V).homology 2 ⟶ (bordifiedLocalChains V).homology 3 :=
  ModuleCat.ofHom ((relativeCochainCapHomology boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V 2 3).flip
      SymmetricSpaceRelativeFundamental.fundamentalClass)

/-- The actual boundary cohomology connecting map into geometric relative cohomology. -/
abbrev geometricBoundaryConnecting (V : Rep.{0} ℚ principalSix) (a : ℕ) :=
  RelativeCochainSequence.connecting (geometricBoundaryRestriction V) a

/-- Cap against the actual connecting image of the relative fundamental class. -/
def boundaryFundamentalCap (V : Rep.{0} ℚ principalSix) :
    (localCochains boundaryProjection boundaryQuotientCovering V).homology 1 ⟶
      (boundaryLocalChains V).homology 3 :=
  ModuleCat.ofHom ((absolute boundaryProjection boundaryQuotientCovering V 1 3).flip
    SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass)

/-- The actual compact-pair cap square at H1(boundary), H2(relative), and H3(absolute).
Its positive sign is derived from the actual front/back cap formula and the two LES conventions. -/
theorem fundamental_cap_connecting (V : Rep.{0} ℚ principalSix) :
    boundaryFundamentalCap V ≫ homologyMap (boundaryInclusionMap V) 3 =
      geometricBoundaryConnecting V 1 ≫ relativeFundamentalCap V := by
  let : Mono (scalarSpaceMap boundaryBaseInclusion) :=
    (inferInstance : Mono (RationalRelativeSingular.inclusion (boundary principalSix)))
  let : Epi (SingularCoverNaturality.localPullback boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V) :=
      (inferInstance : Epi (geometricBoundaryRestriction V))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact RelativeCapConnecting.geometric_connecting_cap boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V 1 3 x
    SymmetricSpaceRelativeFundamental.fundamentalClass

end TernaryPoly.SymmetricSpaceRelativeCapConnecting
