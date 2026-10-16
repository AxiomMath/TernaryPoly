module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux00
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux01
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux02
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux03
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux04
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux10
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux11
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux12
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux13
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux14
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux20
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux21
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux22
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux23
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux24
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux30
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux31
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux32
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux33
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux34
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux40
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux41
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux42
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux43
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThreeAux44

@[expose] public section



/-! R3: the exterior derivative (degree three) of `star2to3 a` agrees with `-star1to4` of the
metric contraction of `a`, for alternating `a`. Assembled from the 25 two-leading-index slices
`hodgeStarRule_three_aux00`..`hodgeStarRule_three_aux44`, each independently checked. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem hodgeStarRule_three (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    exteriorThree (star2to3 a) = -star1to4 (contractionTwo a) := by
  funext i j k l
  fin_cases i <;> fin_cases j
  · exact hodgeStarRule_three_aux00 a ha k l
  · exact hodgeStarRule_three_aux01 a ha k l
  · exact hodgeStarRule_three_aux02 a ha k l
  · exact hodgeStarRule_three_aux03 a ha k l
  · exact hodgeStarRule_three_aux04 a ha k l
  · exact hodgeStarRule_three_aux10 a ha k l
  · exact hodgeStarRule_three_aux11 a ha k l
  · exact hodgeStarRule_three_aux12 a ha k l
  · exact hodgeStarRule_three_aux13 a ha k l
  · exact hodgeStarRule_three_aux14 a ha k l
  · exact hodgeStarRule_three_aux20 a ha k l
  · exact hodgeStarRule_three_aux21 a ha k l
  · exact hodgeStarRule_three_aux22 a ha k l
  · exact hodgeStarRule_three_aux23 a ha k l
  · exact hodgeStarRule_three_aux24 a ha k l
  · exact hodgeStarRule_three_aux30 a ha k l
  · exact hodgeStarRule_three_aux31 a ha k l
  · exact hodgeStarRule_three_aux32 a ha k l
  · exact hodgeStarRule_three_aux33 a ha k l
  · exact hodgeStarRule_three_aux34 a ha k l
  · exact hodgeStarRule_three_aux40 a ha k l
  · exact hodgeStarRule_three_aux41 a ha k l
  · exact hodgeStarRule_three_aux42 a ha k l
  · exact hodgeStarRule_three_aux43 a ha k l
  · exact hodgeStarRule_three_aux44 a ha k l

end TernaryPeriodPolynomials.Argument.Coercivity
