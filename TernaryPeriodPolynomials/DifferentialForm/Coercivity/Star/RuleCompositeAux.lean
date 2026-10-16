module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFour

@[expose] public section



/-! Two linearity helper lemmas needed to assemble the COMPOSITE identity
`algebraicHodgeThree (star2to3 a) = star2to3 (algebraicHodgeTwo a)` from R1-R4 without a fresh
case split: additivity of `star2to3`, and compatibility of `contractionFour` with negation. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star2to3_add (x y : TwoCoordinates) :
    star2to3 (x + y) = star2to3 x + star2to3 y := by
  funext i j k
  simp [star2to3, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem contractionFour_neg (x : FourCoordinates) :
    contractionFour (-x) = -contractionFour x := by
  funext i j k
  simp [contractionFour, Pi.neg_apply, map_neg, smul_neg, Finset.sum_neg_distrib]

end TernaryPeriodPolynomials.Argument.Coercivity
