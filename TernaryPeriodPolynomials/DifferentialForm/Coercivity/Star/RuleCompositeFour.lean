module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleCompositeFourAux
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFour

@[expose] public section



/-! The degree-four composite Hodge-star identity `H₄ ∘ ⋆₁ = ⋆₁ ∘ H₁`, assembled from R0
(`exteriorFour_star1to4`), R3 (`hodgeStarRule_three`), R4 (`hodgeStarRule_four`), R5
(`contractionFive_star1to4`), and the two linearity helpers in `StarRuleCompositeFourAux.lean`,
mirroring `StarRuleComposite.lean`'s degree-two/three template one level up. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity
open TernaryPeriodPolynomials.Argument.CoercivityOne

theorem algebraicHodgeFour_star1to4 (β : OneCoordinates) :
    algebraicHodgeFour (star1to4 β) = star1to4 (algebraicHodgeOne β) := by
  simp only [algebraicHodgeFour, algebraicHodgeOne]
  rw [star1to4_add, hodgeStarRule_four β, exteriorThree_neg,
    hodgeStarRule_three (exteriorOne β) (exteriorOne_alternating β), neg_neg,
    exteriorFour_star1to4 β, contractionFive_star1to4 (contractionOne β)]
  abel

end TernaryPeriodPolynomials.Argument.Coercivity
