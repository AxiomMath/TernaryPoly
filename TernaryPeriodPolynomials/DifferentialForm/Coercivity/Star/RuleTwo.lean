module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleTwoAux0
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleTwoAux1
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleTwoAux2
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleTwoAux3
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleTwoAux4

@[expose] public section



/-! R2: the exterior derivative of `star3to2 b` agrees with `star2to3` of the metric contraction
of `b`, for alternating `b`. Assembled from the five first-index slices
`hodgeStarRule_two_aux0`..`hodgeStarRule_two_aux4`, each independently checked. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem hodgeStarRule_two (b : ThreeCoordinates) (hb : IsAlternatingThree b) :
    exteriorTwo (star3to2 b) = star2to3 (contractionThree b) := by
  funext i j k
  fin_cases i
  · exact hodgeStarRule_two_aux0 b hb j k
  · exact hodgeStarRule_two_aux1 b hb j k
  · exact hodgeStarRule_two_aux2 b hb j k
  · exact hodgeStarRule_two_aux3 b hb j k
  · exact hodgeStarRule_two_aux4 b hb j k

end TernaryPeriodPolynomials.Argument.Coercivity
