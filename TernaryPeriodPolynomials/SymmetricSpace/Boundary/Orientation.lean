module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.OrientationNonzero

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryOrientation
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular RationalLocalChartHomology RationalLocalOrientation
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open SingularBoundaryRestriction HalfSpaceBoundaryOrientation SymmetricSpaceBoundaryManifold

/-- The actual entire boundary carries the homological orientation induced by the literal
connecting image of the fixed arithmetic relative fundamental class. -/
def boundaryOrientation : Orientation 4 BoundaryBase where
  generator := boundaryGenerator
  nonzero := boundaryGenerator_nonzero
  locallyRepresented := boundaryGenerator_locallyRepresented

/-- No new local generators are chosen when packaging the actual boundary orientation. -/
theorem boundaryOrientation_generator (x : BoundaryBase) :
    boundaryOrientation.generator x = boundaryGenerator x := rfl

/-- The global connecting class restricts to exactly the packaged actual boundary generators. -/
theorem boundaryFundamentalClass_at_point (x : BoundaryBase) :
    homologyMap (absolutePointProjection x) 4 boundaryFundamentalClass =
      boundaryOrientation.generator x := rfl

/-- The actual compact whole-boundary class is exactly the literal whole-support image
of the connecting class, with the induced orientation and no additional scalar. -/
theorem boundaryCompactFundamentalClass_eq_projection :
    RationalManifoldCompact.compactFundamentalClass 2 boundaryEuclidean boundaryOrientation
      Set.univ isCompact_univ = homologyMap absoluteSupportProjection 4 boundaryFundamentalClass :=
  compactFundamentalClass_eq_projection 2 boundaryEuclidean boundaryFundamentalClass
    boundaryGenerator_nonzero

/-- The ordinary compact boundary fundamental class agrees with the actual connecting class
under the literal absolute/whole-support identification. -/
theorem boundaryFundamentalClass_eq_ordinary :
    boundaryFundamentalClass = ordinaryFundamentalClass 2 boundaryEuclidean boundaryOrientation :=
  (ordinaryFundamentalClass_orientationOfGlobal 2 boundaryEuclidean boundaryFundamentalClass
    boundaryGenerator_nonzero).symm

/-- The original boundary class is recovered by the literal inverse whole-support projection. -/
theorem boundaryFundamentalClass_eq_support_inverse :
    boundaryFundamentalClass = (absoluteSupportHomologyIso 4).inv
      (RationalManifoldCompact.compactFundamentalClass 2 boundaryEuclidean boundaryOrientation
        Set.univ isCompact_univ) := boundaryFundamentalClass_eq_ordinary

end TernaryPoly.SymmetricSpaceBoundaryOrientation
