module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AltExtension
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.OneFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! First-index-4 slice of the two-sided involution helper `star3to2 (star2to3 a) = (1/96) • a`
(see `StarTwoSideSelf.lean`), split by first index `i` as in `StarTwoSideSelfAux0.lean`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star3to2_star2to3_self_aux4 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (j : Fin 5) :
    star3to2 (star2to3 a) 4 j = (1/96 : ℝ) • a 4 j := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases j <;> simp only [star3to2, Fin.sum_univ_five]
  all_goals simp
  all_goals simp [star2to3, altTwo, Fin.sum_univ_five, tangentWeight]
  all_goals module

end TernaryPeriodPolynomials.Argument.Coercivity
