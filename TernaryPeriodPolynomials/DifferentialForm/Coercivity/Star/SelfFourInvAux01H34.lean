module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvDup

@[expose] public section



/-! Single hard `(k, l) = (3, 4)` branch of the `0, 1`-slice of the involution
`star1to4 (star4to1 a) = (1/96) • a`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_star4to1_self_aux01_34 (a : FourCoordinates) (ha : IsAlternatingFour a) :
    star1to4 (star4to1 a) 0 1 3 4 = (1 / 96 : ℝ) • a 0 1 3 4 := by
  rw [altFour_eq_of_alternating ha,
    star1to4_eq_single _ 0 1 3 4 2 (by intro m' hm'; fin_cases m' <;> simp_all)]
  simp [star4to1, altFour, altThree, Fin.sum_univ_five, tangentWeight]
  module

end TernaryPeriodPolynomials.Argument.Coercivity
