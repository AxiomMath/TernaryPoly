module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvDup

@[expose] public section



/-! Single hard `(k, l) = (3, 1)` branch of the `0, 4`-slice of the involution
`star1to4 (star4to1 a) = (1/96) • a`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_star4to1_self_aux04_31 (a : FourCoordinates) (ha : IsAlternatingFour a) :
    star1to4 (star4to1 a) 0 4 3 1 = (1 / 96 : ℝ) • a 0 4 3 1 := by
  rw [altFour_eq_of_alternating ha,
    star1to4_eq_single _ 0 4 3 1 2 (by intro m' hm'; fin_cases m' <;> simp_all)]
  simp [star4to1, altFour, altThree, Fin.sum_univ_five, tangentWeight]
  module

end TernaryPeriodPolynomials.Argument.Coercivity
