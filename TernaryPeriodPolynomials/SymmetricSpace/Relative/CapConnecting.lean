module

public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapConnectingOrientation
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapConnectingSupport
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Orientation

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeCapConnecting
open CategoryTheory HomologicalComplex IntegralGL3Congruence
open SingularLocalHomology SingularBoundaryRestriction SymmetricSpaceBoundaryManifold
open SymmetricSpaceBoundaryOrientation SymmetricSpaceBordifiedQuotient

/-- The actual induced boundary orientation identifies ordinary boundary cap with the literal
cap against the connecting image of the uniquely normalized relative fundamental class. -/
theorem actual_boundary_cap_eq_fundamental (V : Rep.{0} ℚ principalSix) :
    (boundaryH1CapIso V boundaryOrientation).hom = boundaryFundamentalCap V :=
  boundaryOrdinaryCap_eq_fundamental V boundaryOrientation boundaryFundamentalClass_eq_ordinary.symm

/-- The genuine ordinary boundary/relative cap connecting square on the actual compact
bordification, for every rational principal-six local coefficient representation. -/
theorem ordinary_cap_connecting (V : Rep.{0} ℚ principalSix) :
    (boundaryH1CapIso V boundaryOrientation).hom ≫ homologyMap (boundaryInclusionMap V) 3 =
      geometricBoundaryConnecting V 1 ≫ relativeFundamentalCap V := by
  rw [actual_boundary_cap_eq_fundamental,fundamental_cap_connecting]

/-- The same actual square in the support model used by compact-interior relative duality. -/
theorem ordinary_cap_support_connecting (V : Rep.{0} ℚ principalSix) :
    (boundaryH1CapIso V boundaryOrientation).hom ≫ homologyMap (boundaryInclusionMap V) 3 =
      geometricBoundaryConnecting V 1 ≫ homologyMap (geometricSupportIso V).hom 2 ≫
        SingularLocalBoundaryCap.boundaryCapMap wholeProjection V (boundary principalSix) 3
          SymmetricSpaceRelativeFundamental.fundamentalClass 2 3 rfl := by
  rw [relativeFundamentalCap_eq_boundaryCapMap]
  exact ordinary_cap_connecting V

end TernaryPoly.SymmetricSpaceRelativeCapConnecting
