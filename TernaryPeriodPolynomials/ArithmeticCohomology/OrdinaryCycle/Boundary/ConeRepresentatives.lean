module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.OrdinaryBoundaryCone

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology
variable {G : Type} [Group G] (A : Rep ℚ G) (P Q : Subgroup G)

/-- Every cohomology class of the explicit cone has an actual cocycle representative. -/
theorem classOf_surjective : Function.Surjective (classOf A P Q) :=
  Submodule.Quotient.mk_surjective (boundaries A P Q)

end TernaryPoly.OrdinaryBoundaryCone
