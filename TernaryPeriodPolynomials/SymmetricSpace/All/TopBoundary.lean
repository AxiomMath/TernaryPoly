module

public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryCap
public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryComparison
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Duality

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceAllTopBoundary
open CompactInteriorRelativeBoundary
open CategoryTheory HomologicalComplex IntegralGL3Congruence
open SingularLocalHomology SingularLocalSupport SymmetricSpaceBordifiedCohomology
open SymmetricSpaceBoundaryDuality

/-- Every actual boundary H3 class is sufficient exactly when genuine compact support
forgetting vanishes in interior degree two, with the identical representation V. -/
theorem boundary_surjective_iff_compactForget_zero (V : Rep.{0} ℚ principalSix) :
    Function.Surjective (homologyMap (boundaryInclusionMap V) 3).hom ↔
      compactForget interiorCover V 2 = 0 :=
  (boundary_surjective_iff_geometric_relative_zero V).trans
    (geometric_relative_zero_iff_compactForget_zero V 2)

/-- Actual boundary surjectivity onto group H3 is equivalent to degree-two compactForget
vanishing for the same arithmetic local coefficient system. -/
theorem boundaryToGroup_surjective_iff_compactForget_zero (V : Rep.{0} ℚ principalSix) :
    Function.Surjective (boundaryToGroup V 3).hom ↔ compactForget interiorCover V 2 = 0 :=
  (boundaryToGroup_surjective_iff V 3).trans (boundary_surjective_iff_compactForget_zero V)

/-- Genuine inner cohomology is the image of the actual compact-support-to-ordinary map. -/
def innerCohomology (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    Submodule ℚ ((SingularLocalCoefficient.localCochains interiorCover
      interiorCover_isQuotientCovering V).homology k) :=
  LinearMap.range (compactForget interiorCover V k).hom

/-- Zero genuine inner cohomology means exactly that its actual support-forgetting map is zero. -/
theorem innerCohomology_eq_bot_iff (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    innerCohomology V k = ⊥ ↔ compactForget interiorCover V k = 0 := by
  rw [innerCohomology,LinearMap.range_eq_bot]
  exact ModuleCat.hom_ext_iff.symm

/-- The precise all-top-boundary equivalence with degree-two inner cohomology. -/
theorem boundaryToGroup_surjective_iff_inner_degree_two_zero (V : Rep.{0} ℚ principalSix) :
    Function.Surjective (boundaryToGroup V 3).hom ↔ innerCohomology V 2 = ⊥ :=
  (boundaryToGroup_surjective_iff_compactForget_zero V).trans (innerCohomology_eq_bot_iff V 2).symm

end TernaryPoly.SymmetricSpaceAllTopBoundary
