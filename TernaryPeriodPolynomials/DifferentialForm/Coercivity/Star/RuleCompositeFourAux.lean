module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFive
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFiveB

@[expose] public section



/-! Two linearity helper lemmas needed to assemble the degree-four COMPOSITE identity
`algebraicHodgeFour (star1to4 β) = star1to4 (algebraicHodgeOne β)` from R0, R3, R4, R5 without a
fresh case split: additivity of `star1to4`, and compatibility of `exteriorThree` with negation.
Mirrors `StarRuleCompositeAux.lean`'s `star2to3_add`/`contractionFour_neg` one degree up. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_add (x y : OneCoordinates) :
    star1to4 (x + y) = star1to4 x + star1to4 y := by
  funext i j k l
  simp [star1to4, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem exteriorThree_neg (x : ThreeCoordinates) :
    exteriorThree (-x) = -exteriorThree x := by
  funext i j k l
  simp only [exteriorThree, Pi.neg_apply, map_neg]
  abel

end TernaryPeriodPolynomials.Argument.Coercivity
