module

public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryLES
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapConnecting
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapComparison

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceAllTopBoundary
open CategoryTheory HomologicalComplex IntegralGL3Congruence
open SingularBoundaryRestriction SingularLocalHomology SymmetricSpaceBoundaryManifold
open SymmetricSpaceBoundaryOrientation SymmetricSpaceRelativeCapConnecting

/-- The actual geometric relative fundamental cap is an isomorphism through its exact
identity-on-representatives comparison to the proved support-model relative cap. -/
instance relativeFundamentalCap_isIso (V : Rep.{0} ℚ principalSix) :
    IsIso (relativeFundamentalCap V) := by
  have h := SymmetricSpaceRelativeCap.relativeCapMap_isIso V 2 3 rfl
  rw [← relativeFundamentalCap_eq_boundaryCapMap V]
  change IsIso (homologyMap (geometricSupportIso V).hom 2 ≫
    SymmetricSpaceRelativeCap.relativeCapMap V 2 3 rfl)
  infer_instance

/-- The actual H3 boundary inclusion is onto exactly when the genuine H1-to-H2 cohomology
connecting map is onto, with precisely the same local coefficient representation. -/
theorem boundary_surjective_iff_connecting_surjective (V : Rep.{0} ℚ principalSix) :
    Function.Surjective (homologyMap (boundaryInclusionMap V) 3).hom ↔
      Function.Surjective (geometricBoundaryConnecting V 1).hom :=
  surjective_iff_of_iso_square (boundaryH1CapIso V boundaryOrientation)
    (asIso (relativeFundamentalCap V)) (homologyMap (boundaryInclusionMap V) 3)
    (geometricBoundaryConnecting V 1) (ordinary_cap_connecting V)

/-- Actual H3 boundary surjectivity is exactly zero of the genuine relative H2 map,
without dualizing or changing the coefficient representation. -/
theorem boundary_surjective_iff_geometric_relative_zero (V : Rep.{0} ℚ principalSix) :
    Function.Surjective (homologyMap (boundaryInclusionMap V) 3).hom ↔
      RelativeCochainSequence.relativeMap (geometricBoundaryRestriction V) 2 = 0 :=
  (boundary_surjective_iff_connecting_surjective V).trans
    (connecting_surjective_iff_relative_zero (geometricBoundaryRestriction V) 1)

end TernaryPoly.SymmetricSpaceAllTopBoundary
