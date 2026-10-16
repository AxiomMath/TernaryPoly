module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFourAux0
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFourAux1
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFourAux2
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFourAux3
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFourAux4

@[expose] public section



/-! R4: the metric contraction (degree four to three) of `star1to4 β` agrees with `-star2to3` of
the exterior derivative of `β`, for arbitrary `β : OneCoordinates` (no alternating hypothesis is
possible or needed in degree one). Assembled from the five first-index slices
`hodgeStarRule_four_aux0`..`hodgeStarRule_four_aux4`, each independently checked. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem hodgeStarRule_four (β : OneCoordinates) :
    contractionFour (star1to4 β) = -star2to3 (exteriorOne β) := by
  funext i j k
  fin_cases i
  · exact hodgeStarRule_four_aux0 β j k
  · exact hodgeStarRule_four_aux1 β j k
  · exact hodgeStarRule_four_aux2 β j k
  · exact hodgeStarRule_four_aux3 β j k
  · exact hodgeStarRule_four_aux4 β j k

end TernaryPeriodPolynomials.Argument.Coercivity
