module

public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationHomeomorph
public import TernaryPeriodPolynomials.Topology.Euclidean.Local.OrientationSection
public import TernaryPeriodPolynomials.SymmetricSpace.LocalOrientationPositive

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceLocalOrientation
open RationalLocalOrientation SymmetricSpacePositive SymmetricSpaceEuclideanCoordinates

/-- The actual point generators on the positive-form space form a locally represented section. -/
theorem localGenerator_locallyRepresented : LocallyRepresented 5 localGenerator :=
  locallyRepresented_pullback spaceHomeomorph 5 (EuclideanLocalHomology.localGenerator 3)
    (EuclideanLocalHomology.localGenerator_locallyRepresented 3)

/-- The actual positive-form space has a homological orientation with genuine relative-class
representatives, using its global Euclidean coordinates. -/
def spaceOrientation : Orientation 5 Space where
  generator := localGenerator
  nonzero := localGenerator_ne_zero
  locallyRepresented := localGenerator_locallyRepresented

end TernaryPoly.SymmetricSpaceLocalOrientation
