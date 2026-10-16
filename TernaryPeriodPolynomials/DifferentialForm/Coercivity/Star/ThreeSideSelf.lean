module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.ThreeSideSelfAux0
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.ThreeSideSelfAux1
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.ThreeSideSelfAux2
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.ThreeSideSelfAux3
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.ThreeSideSelfAux4

@[expose] public section



/-! Three-sided involution helper for INVOLUTION: `star2to3 (star3to2 b) = (1/96) • b` for
alternating `b : ThreeCoordinates`. Assembled from the five first-index slices
(`star2to3_star3to2_self_aux0` through `_aux4`, each in its own `StarThreeSideSelfAux{I}.lean`),
dispatched on the first free output index `i` by `fin_cases`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star2to3_star3to2_self (b : ThreeCoordinates) (hb : IsAlternatingThree b) :
    star2to3 (star3to2 b) = (1/96 : ℝ) • b := by
  funext i j k
  fin_cases i
  · exact star2to3_star3to2_self_aux0 b hb j k
  · exact star2to3_star3to2_self_aux1 b hb j k
  · exact star2to3_star3to2_self_aux2 b hb j k
  · exact star2to3_star3to2_self_aux3 b hb j k
  · exact star2to3_star3to2_self_aux4 b hb j k

end TernaryPeriodPolynomials.Argument.Coercivity
