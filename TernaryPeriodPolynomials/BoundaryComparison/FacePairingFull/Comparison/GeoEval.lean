module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryH4

@[expose] public section


/-!
# The geometric evaluation on the boundary fundamental class

`geoIso : H⁴(stabilizerTotalCochains ℚ) ≅ ℚ` is the composite of the identification of the stabilizer cone
with the local-system cochains of `∂M` (`localBoundaryToStabilizerTotal`), the Poincaré duality cap product
with the fundamental class of `boundaryOrientation` (`boundaryOrdinaryCapIso`; this orientation is that of
`boundaryFundamentalClass`, `boundaryOrientation_class`) and the augmentation `H₀(∂M; ℚ) ≅ ℚ`
(`boundaryH0Iso`, `TopHomology.trivialLocalH0Iso`).  It is the definition behind `stabilizerTotal_H4_iso`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex
open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceBoundaryGeometricCone TernaryPoly.SymmetricSpaceBoundaryManifold
  TernaryPoly.SymmetricSpaceBoundaryOrientation TernaryPoly.HalfSpaceBoundaryOrientation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPeriodPolynomials.Argument.TopHomology

/-- `H₀` of the trivial rational local system of the boundary is `ℚ` (the augmentation). -/
def boundaryH0Iso :
    (SingularLocalCompactCap.coveringLocalChains boundaryProjection trivialW).homology 0 ≅
      ModuleCat.of ℚ ℚ :=
  haveI : IsCancelSMul principalSix BoundaryCover := boundaryQuotientCovering.isCancelSMul
  trivialLocalH0Iso boundaryProjection boundaryQuotientCovering trivialW_action

/-- **The geometric evaluation of top cohomology classes on the boundary fundamental class.**
Poincaré duality of the closed oriented 4-manifold `∂M` caps a class of `H⁴` with the fundamental class of
the orientation `boundaryOrientation` (that of `boundaryFundamentalClass`), landing in `H₀`, followed by the
augmentation `H₀ ≅ ℚ`; the total stabilizer cone computes `H⁴(∂M; ℚ)` (`localBoundaryToStabilizerTotal`). -/
def geoIso : (stabilizerTotalCochains trivialW).homology 4 ≅ ModuleCat.of ℚ ℚ :=
  haveI : IsIso (homologyMap (localBoundaryToStabilizerTotal trivialW) 4) := inferInstance
  (asIso (homologyMap (localBoundaryToStabilizerTotal trivialW) 4)).symm ≪≫
    boundaryOrdinaryCapIso trivialW boundaryOrientation 4 0 rfl ≪≫ boundaryH0Iso

/-- The orientation used in `geoIso` is the one of the boundary fundamental class. -/
theorem boundaryOrientation_class :
    boundaryFundamentalClass = ordinaryFundamentalClass 2 boundaryEuclidean boundaryOrientation :=
  boundaryFundamentalClass_eq_ordinary

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
