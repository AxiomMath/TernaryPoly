module

public import TernaryPeriodPolynomials.SymmetricSpace.Relative.FundamentalClass
public import TernaryPeriodPolynomials.Topology.Rational.Compact.BoundaryRestriction

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeFundamental
open CategoryTheory HomologicalComplex RationalRelativeSingular
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open RationalCompactBoundary BoundaryNeighborhood

/-- Restriction of the actual arithmetic relative fundamental class to any compact interior
support is precisely the actual compact fundamental class of the arithmetic orientation. -/
theorem fundamentalClass_restriction (K : Set BordifiedOrbit) (hK : IsCompact K)
    (hKA : K ⊆ (boundary principalSix)ᶜ) :
    homologyMap (toNeighborhoodRelative (boundary principalSix) Kᶜ
      (fun _ ha hk => hKA hk ha)) 5 fundamentalClass =
      interiorFundamentalClass (boundary principalSix) (boundary_closed principalSix)
        3 interiorEuclidean interiorOrientation K hK hKA :=
  restriction_eq_interiorFundamentalClass (boundary principalSix) (boundary_closed principalSix)
    3 interiorEuclidean interiorOrientation fundamentalClass fundamentalClass_at_point K hK hKA

end TernaryPoly.SymmetricSpaceRelativeFundamental
