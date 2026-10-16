module

public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapConnectingCore
public import TernaryPeriodPolynomials.GroupCohomology.Relative.CapConnectingCompactAbsolute
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Manifold

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeCapConnecting
open CategoryTheory HomologicalComplex IntegralGL3Congruence
open SingularBoundaryRestriction SingularLocalCoefficient SingularLocalHomology
open RationalLocalOrientation HalfSpaceBoundaryOrientation SymmetricSpaceBoundaryManifold

/-- Any supplied boundary orientation whose genuine ordinary fundamental class is the literal
connecting image gives precisely the actual absolute boundary cap. -/
theorem boundaryOrdinaryCap_eq_fundamental (V : Rep.{0} ℚ principalSix)
    (o : Orientation 4 (TopCat.of BoundaryBase))
    (ho : ordinaryFundamentalClass 2 boundaryEuclidean o =
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass) :
    (boundaryH1CapIso V o).hom = boundaryFundamentalCap V := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change CompactOrdinaryCap.ordinaryCapMap boundaryProjection V 2 boundaryEuclidean o 1 3 rfl x =
    SingularLocalCap.absolute boundaryProjection boundaryQuotientCovering V 1 3 x
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass
  have h := RelativeCapConnecting.ordinaryCap_eq_absolute boundaryProjection V 2 boundaryEuclidean o
    1 3 rfl x
  simpa only [SingularLocalCompactCap.homologyDegreeChange,eqToHom_refl,ModuleCat.id_apply,ho] using h

/-- The ordinary H1(boundary)-to-H3(boundary) cap and the genuine H2(relative)-to-H3(absolute)
cap form the actual connecting square once the boundary orientation is identified literally. -/
theorem ordinary_cap_connecting_of_fundamental (V : Rep.{0} ℚ principalSix)
    (o : Orientation 4 (TopCat.of BoundaryBase))
    (ho : ordinaryFundamentalClass 2 boundaryEuclidean o =
      SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass) :
    (boundaryH1CapIso V o).hom ≫ homologyMap (boundaryInclusionMap V) 3 =
      geometricBoundaryConnecting V 1 ≫ relativeFundamentalCap V := by
  rw [boundaryOrdinaryCap_eq_fundamental V o ho,fundamental_cap_connecting]

end TernaryPoly.SymmetricSpaceRelativeCapConnecting
