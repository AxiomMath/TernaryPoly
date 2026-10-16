module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.Generators
public import TernaryPeriodPolynomials.SymmetricSpace.Orientation.Section
public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationDescent

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientOrientation
open RationalLocalOrientation SymmetricSpaceCovering

/-- The actual quotient local generators admit genuine relative-class representatives on
neighborhoods, obtained by closed-support excision in embedding neighborhoods of the covering. -/
theorem localGenerator_locallyRepresented : LocallyRepresented 5 localGenerator :=
  locallyRepresented_pushforward projection projection_localHomeomorph quotientProjection_surjective 5
    SymmetricSpaceLocalOrientation.localGenerator
    SymmetricSpaceLocalOrientation.localGenerator_locallyRepresented
    localGenerator localGenerator_projection

/-- The actual arithmetic quotient carries a genuine homological orientation: each generator is
nonzero, every lift induces that generator, and nearby generators share a relative representative. -/
def quotientOrientation : Orientation 5 OrbitSpace where
  generator := localGenerator
  nonzero := localGenerator_ne_zero
  locallyRepresented := localGenerator_locallyRepresented

end TernaryPoly.SymmetricSpaceQuotientOrientation
