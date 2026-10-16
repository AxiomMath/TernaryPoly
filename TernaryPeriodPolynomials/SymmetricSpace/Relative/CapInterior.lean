module

public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapGeometry
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.FundamentalRestriction
public import TernaryPeriodPolynomials.Topology.SingularLocal.BoundaryCapSupport
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Duality

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeCap
open CategoryTheory HomologicalComplex TopologicalSpace
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open SymmetricSpaceRelativeFundamental SingularBoundaryRestriction RationalCompactBoundary
open SingularLocalSupport SingularLocalCompactCap SingularLocalHomology SingularLocalBoundaryCap
open EquivariantSingularSmall

variable (V : Rep.{0} ℚ principalSix)

/-- The actual arithmetic relative cap, with the constructed arithmetic relative fundamental class. -/
def relativeCapMap (a b : ℕ) (hab : a+b = 5) :
    (supportCochains wholeProjection V (boundary principalSix)ᶜ).homology a ⟶
      (coveringLocalChains wholeProjection V).homology b := by
  letI := wholeQuotientCovering.isCancelSMul
  exact boundaryCapMap wholeProjection V (boundary principalSix) 3 fundamentalClass a b hab

/-- The actual interior compact cap is an isomorphism for all complementary degrees and
arbitrary rational principal-six representations. -/
theorem interiorCompactCap_isIso (a b : ℕ) (hab : a+b = 5) :
    IsIso (compactCapMap interiorProjection V 3 interiorEuclidean interiorOrientation a b hab) :=
  SingularLocalCompactDuality.manifold_compactCap_isIso interiorProjection V
    3 interiorEuclidean interiorOrientation a b hab

/-- Actual interior compact cap followed by actual inclusion into the bordification. -/
def interiorCapToBordified (a b : ℕ) (hab : a+b = 5) :
    compactCohomology interiorProjection V a ⟶ (coveringLocalChains wholeProjection V).homology b :=
  compactCapMap interiorProjection V 3 interiorEuclidean interiorOrientation a b hab ≫
    homologyMap (openLocalChainMap wholeProjection V (boundary principalSix)ᶜ) b

/-- The actual interior compact-cap-and-inclusion map is an isomorphism. -/
theorem interiorCapToBordified_isIso (a b : ℕ) (hab : a+b = 5) :
    IsIso (interiorCapToBordified V a b hab) := by
  have := interiorCompactCap_isIso V a b hab
  have := interiorLocalInclusion_isIso V b
  unfold interiorCapToBordified
  infer_instance

/-- Every compact support sees the same actual relative cap and interior compact cap. -/
theorem relativeCapMap_support (K : Set BordifiedOrbit) (hK : IsCompact K)
    (hKA : K ⊆ (boundary principalSix)ᶜ) (a b : ℕ) (hab : a+b = 5) :
    homologyMap (supportMap wholeProjection V K (boundary principalSix)ᶜ hKA) a ≫
      relativeCapMap V a b hab =
      homologyMap (supportToOpen wholeProjection V (boundary principalSix)ᶜ K) a ≫
        compactCapAt interiorProjection V 3 interiorEuclidean interiorOrientation
          ⟨Subtype.val ⁻¹' K,
            interiorCompact (boundary principalSix) (boundary_closed principalSix) K hK hKA⟩ a b hab ≫
          homologyMap (openLocalChainMap wholeProjection V (boundary principalSix)ᶜ) b := by
  let : IsCancelSMul principalSix SymmetricSpaceRationalGluing.Glued := wholeQuotientCovering.isCancelSMul
  exact boundaryCapMap_support wholeProjection V (boundary principalSix) (boundary_closed principalSix)
    3 interiorEuclidean interiorOrientation fundamentalClass fundamentalClass_at_point K hK hKA a b hab

end TernaryPoly.SymmetricSpaceRelativeCap
