module

public import TernaryPeriodPolynomials.SymmetricSpace.Relative.FundamentalGeometry
public import TernaryPeriodPolynomials.Topology.Rational.Compact.BoundaryUnique
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Neighborhood

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeFundamental
open CategoryTheory HomologicalComplex RationalRelativeSingular RationalRelativeExcision
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open RationalCompactBoundary

/-- The actual compact arithmetic bordification has a unique rational relative fundamental
class with the literal transported arithmetic orientation at every interior point. -/
theorem existsUnique_fundamentalClass :
    ∃! c : (relativeChains (boundary principalSix)).homology 5,
      ∀ x (hx : x ∉ boundary principalSix),
        homologyMap (boundaryPointMap (boundary principalSix) x hx) 5 c =
          homologyMap (pointExcisionMap x (boundary principalSix)ᶜ hx) 5
            (interiorOrientation.generator ⟨x,hx⟩) := by
  let c := SymmetricSpaceBoundaryNeighborhood.collapse Set.univ isOpen_univ (Set.subset_univ _)
  exact existsUnique_relativeFundamentalClass (boundary principalSix) (boundary_closed principalSix)
    3 interiorEuclidean interiorOrientation c.deformation c.neighborhood c.isOpen
    c.contains_boundary c.collapses

/-- The actual relative fundamental class, chosen from its proved unique characterization. -/
def fundamentalClass : (relativeChains (boundary principalSix)).homology 5 :=
  existsUnique_fundamentalClass.choose

/-- Every actual interior point sees precisely the specified arithmetic orientation. -/
theorem fundamentalClass_at_point (x : BordifiedOrbit) (hx : x ∉ boundary principalSix) :
    homologyMap (boundaryPointMap (boundary principalSix) x hx) 5 fundamentalClass =
      homologyMap (pointExcisionMap x (boundary principalSix)ᶜ hx) 5
        (interiorOrientation.generator ⟨x,hx⟩) :=
  existsUnique_fundamentalClass.choose_spec.1 x hx

/-- The actual point restrictions uniquely characterize the relative fundamental class. -/
theorem fundamentalClass_unique (c : (relativeChains (boundary principalSix)).homology 5)
    (hc : ∀ x (hx : x ∉ boundary principalSix),
      homologyMap (boundaryPointMap (boundary principalSix) x hx) 5 c =
        homologyMap (pointExcisionMap x (boundary principalSix)ᶜ hx) 5
          (interiorOrientation.generator ⟨x,hx⟩)) : c = fundamentalClass :=
  existsUnique_fundamentalClass.choose_spec.2 c hc

end TernaryPoly.SymmetricSpaceRelativeFundamental
