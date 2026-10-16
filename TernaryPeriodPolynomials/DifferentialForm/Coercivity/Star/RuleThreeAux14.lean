module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AltExtension
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.OneFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! R3, leading indices fixed to `(1, 4)`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

private theorem hodgeStarRule_three_aux14_k0 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (l : Fin 5) :
    exteriorThree (star2to3 a) 1 4 0 l = -star1to4 (contractionTwo a) 1 4 0 l := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases l <;>
    simp [exteriorThree, star2to3, star1to4, contractionTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_three_aux14_k1 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (l : Fin 5) :
    exteriorThree (star2to3 a) 1 4 1 l = -star1to4 (contractionTwo a) 1 4 1 l := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases l <;>
    simp [exteriorThree, star2to3, star1to4, contractionTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_three_aux14_k2 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (l : Fin 5) :
    exteriorThree (star2to3 a) 1 4 2 l = -star1to4 (contractionTwo a) 1 4 2 l := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases l <;>
    simp [exteriorThree, star2to3, star1to4, contractionTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_three_aux14_k3 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (l : Fin 5) :
    exteriorThree (star2to3 a) 1 4 3 l = -star1to4 (contractionTwo a) 1 4 3 l := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases l <;>
    simp [exteriorThree, star2to3, star1to4, contractionTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_three_aux14_k4 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (l : Fin 5) :
    exteriorThree (star2to3 a) 1 4 4 l = -star1to4 (contractionTwo a) 1 4 4 l := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases l <;>
    simp [exteriorThree, star2to3, star1to4, contractionTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg]

theorem hodgeStarRule_three_aux14 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (k l : Fin 5) :
    exteriorThree (star2to3 a) 1 4 k l = -star1to4 (contractionTwo a) 1 4 k l := by
  fin_cases k
  · exact hodgeStarRule_three_aux14_k0 a ha l
  · exact hodgeStarRule_three_aux14_k1 a ha l
  · exact hodgeStarRule_three_aux14_k2 a ha l
  · exact hodgeStarRule_three_aux14_k3 a ha l
  · exact hodgeStarRule_three_aux14_k4 a ha l

end TernaryPeriodPolynomials.Argument.Coercivity
