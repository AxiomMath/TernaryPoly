module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ManifoldCap

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryManifold
open CategoryTheory IntegralGL3Congruence SingularBoundaryRestriction
  SingularLocalCoefficient SingularLocalCompactCap RationalLocalOrientation

/-- The actual ordinary boundary H1-to-H3 cap isomorphism for a supplied genuine orientation.
This uses arbitrary rational local coefficients and the literal boundary covering. -/
def boundaryH1CapIso (V : Rep.{0} ℚ principalSix)
    (o : Orientation 4 (TopCat.of BoundaryBase)) :
    (localCochains boundaryProjection boundaryQuotientCovering V).homology 1 ≅
      (coveringLocalChains boundaryProjection V).homology 3 :=
  boundaryOrdinaryCapIso V o 1 3 rfl

/-- The specialized H1-to-H3 isomorphism retains the literal supplied-orientation compact cap map. -/
theorem boundaryH1CapIso_compact (V : Rep.{0} ℚ principalSix)
    (o : Orientation 4 (TopCat.of BoundaryBase)) :
    (boundaryCompactOrdinaryIso V 1).hom ≫ (boundaryH1CapIso V o).hom =
      compactCapMap boundaryProjection V 2 boundaryEuclidean o 1 3 rfl :=
  boundary_cap_comparison V o 1 3 rfl

end TernaryPoly.SymmetricSpaceBoundaryManifold
