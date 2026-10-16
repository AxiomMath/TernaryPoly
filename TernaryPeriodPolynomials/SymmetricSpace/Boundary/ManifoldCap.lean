module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ManifoldCharts
public import TernaryPeriodPolynomials.Analysis.Compact.OrdinaryCapDuality

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryManifold
open CategoryTheory HomologicalComplex IntegralGL3Congruence SingularBoundaryRestriction
  SingularLocalCoefficient SingularLocalSupport SingularLocalCompactCap RationalLocalOrientation

/-- The actual whole-boundary projection retains its genuine quotient-covering fact. -/
instance boundaryCoveringFact : Fact (IsQuotientCoveringMap boundaryProjection principalSix) :=
  ⟨boundaryQuotientCovering⟩

variable (V : Rep.{0} ℚ principalSix)

/-- Canonical compact-support-to-ordinary comparison for the literal compact boundary cover. -/
def boundaryCompactOrdinaryIso (a : ℕ) :
    compactCohomology boundaryProjection V a ≅
      (localCochains boundaryProjection boundaryQuotientCovering V).homology a :=
  CompactOrdinaryCap.compactOrdinaryIso boundaryProjection V a

/-- Ordinary cap against a supplied genuine four-dimensional boundary orientation. -/
def boundaryOrdinaryCap (o : Orientation 4 (TopCat.of BoundaryBase))
    (a b : ℕ) (hab : a+b = 4) :
    (localCochains boundaryProjection boundaryQuotientCovering V).homology a ⟶
      (coveringLocalChains boundaryProjection V).homology b :=
  CompactOrdinaryCap.ordinaryCapMap boundaryProjection V 2 boundaryEuclidean o a b hab

/-- Actual compact-boundary ordinary cap is an isomorphism for every supplied orientation and
arbitrary rational principal-six coefficient representation. No orientation is chosen here. -/
instance boundaryOrdinaryCap_isIso (o : Orientation 4 (TopCat.of BoundaryBase))
    (a b : ℕ) (hab : a+b = 4) : IsIso (boundaryOrdinaryCap V o a b hab) :=
  CompactOrdinaryCap.ordinaryCapMap_isIso boundaryProjection V 2 boundaryEuclidean o a b hab

/-- The actual ordinary boundary duality isomorphism, still conditional on the supplied orientation. -/
def boundaryOrdinaryCapIso (o : Orientation 4 (TopCat.of BoundaryBase))
    (a b : ℕ) (hab : a+b = 4) :
    (localCochains boundaryProjection boundaryQuotientCovering V).homology a ≅
      (coveringLocalChains boundaryProjection V).homology b :=
  asIso (boundaryOrdinaryCap V o a b hab)

@[simp] theorem boundaryOrdinaryCapIso_hom (o : Orientation 4 (TopCat.of BoundaryBase))
    (a b : ℕ) (hab : a+b = 4) :
    (boundaryOrdinaryCapIso V o a b hab).hom = boundaryOrdinaryCap V o a b hab := rfl

/-- The boundary ordinary cap retains the exact genuine compact-cap map and its supplied orientation. -/
theorem boundary_cap_comparison (o : Orientation 4 (TopCat.of BoundaryBase))
    (a b : ℕ) (hab : a+b = 4) :
    (boundaryCompactOrdinaryIso V a).hom ≫ boundaryOrdinaryCap V o a b hab =
      compactCapMap boundaryProjection V 2 boundaryEuclidean o a b hab :=
  CompactOrdinaryCap.compactToOrdinary_cap boundaryProjection V 2 boundaryEuclidean o a b hab

/-- Every fixed-support boundary class retains its literal genuine cap pairing. -/
theorem boundaryOrdinaryCap_classMap (o : Orientation 4 (TopCat.of BoundaryBase))
    (K : TopologicalSpace.Compacts (TopCat.of BoundaryBase))
    (a b : ℕ) (hab : a+b = 4) :
    homologyMap (supportInclusion boundaryProjection V (K : Set (TopCat.of BoundaryBase))) a ≫
        boundaryOrdinaryCap V o a b hab =
      compactCapAt boundaryProjection V 2 boundaryEuclidean o K a b hab :=
  CompactOrdinaryCap.ordinaryCap_classMap boundaryProjection V 2 boundaryEuclidean o K a b hab

/-- Ordinary boundary cap is the genuine top-support cap under the exact cochain comparison. -/
theorem boundaryOrdinaryCap_top (o : Orientation 4 (TopCat.of BoundaryBase))
    (a b : ℕ) (hab : a+b = 4) :
    boundaryOrdinaryCap V o a b hab =
      (CompactOrdinaryCap.topSupportHomologyIso boundaryProjection V a).inv ≫
        compactCapAt boundaryProjection V 2 boundaryEuclidean o ⊤ a b hab :=
  CompactOrdinaryCap.ordinaryCap_top boundaryProjection V 2 boundaryEuclidean o a b hab

end TernaryPoly.SymmetricSpaceBoundaryManifold
