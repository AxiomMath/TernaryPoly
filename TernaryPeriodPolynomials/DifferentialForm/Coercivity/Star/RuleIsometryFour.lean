module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.IsometryAdjointFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourUp
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.CasimirOne

@[expose] public section



/-! Degree-one/four analog of `StarRuleIsometry.lean`: the Hodge-star isometry between
`onePairing` and `fourPairing`, UNCONDITIONAL (no alternation hypothesis on either argument,
since both are `OneCoordinates`), assembled from the adjoint relation
(`star4to1_star1to4_adjoint_iso`), the self-identity (`star4to1_star1to4_self`), and
`onePairing_smul_left`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity
open TernaryPeriodPolynomials.Argument.CoercivityOne

theorem hodgeStarRule_isometry_degree_four (β γ : OneCoordinates) :
    fourPairing (star1to4 β) (star1to4 γ) = (1 / 96 : ℝ) * onePairing β γ := by
  rw [← star4to1_star1to4_adjoint_iso (star1to4 β) γ, star4to1_star1to4_self β,
    onePairing_smul_left]

end TernaryPeriodPolynomials.Argument.Coercivity
