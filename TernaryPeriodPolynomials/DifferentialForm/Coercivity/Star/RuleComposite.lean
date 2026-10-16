module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleTwo
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleCompositeAux

@[expose] public section



/-! COMPOSITE: the algebraic Hodge operator at degree three agrees with `star2to3` of the
algebraic Hodge operator at degree two, for alternating `a`. Chained from R1-R4 and the two
linearity helpers (`star2to3_add`, `contractionFour_neg`) rather than a fresh case split:
`algebraicHodgeThree (star2to3 a) = exteriorTwo (contractionThree (star2to3 a))
    + contractionFour (exteriorThree (star2to3 a))`
R1 turns the first summand into `exteriorTwo (star3to2 (exteriorTwo a))`, and R2 (applied to the
alternating `exteriorTwo a`, via `exteriorTwo_alternating`) turns that into
`star2to3 (contractionThree (exteriorTwo a))`, matching one of the two summands of
`star2to3 (algebraicHodgeTwo a)`. R3 turns the second summand into
`contractionFour (-star1to4 (contractionTwo a))`; `contractionFour_neg` and R4 (applied
unconditionally to `contractionTwo a`) turn that into `star2to3 (exteriorOne (contractionTwo a))`,
matching the other summand. `star2to3_add` combines the two target summands, and the two sides
then agree up to `add_comm`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem hodgeStarRule_composite (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    algebraicHodgeThree (star2to3 a) = star2to3 (algebraicHodgeTwo a) := by
  simp only [algebraicHodgeThree, algebraicHodgeTwo]
  rw [star2to3_add, hodgeStarRule_one a ha,
    hodgeStarRule_two (exteriorTwo a) (exteriorTwo_alternating a ha),
    hodgeStarRule_three a ha, contractionFour_neg,
    hodgeStarRule_four (contractionTwo a), neg_neg]
  abel

end TernaryPeriodPolynomials.Argument.Coercivity
