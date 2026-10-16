module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AltExtension
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.OneFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! R3, leading indices fixed to `(0, 0)`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem hodgeStarRule_three_aux00 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (k l : Fin 5) :
    exteriorThree (star2to3 a) 0 0 k l = -star1to4 (contractionTwo a) 0 0 k l := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases k <;> fin_cases l <;>
    simp [exteriorThree, star2to3, star1to4, contractionTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg]

end TernaryPeriodPolynomials.Argument.Coercivity
