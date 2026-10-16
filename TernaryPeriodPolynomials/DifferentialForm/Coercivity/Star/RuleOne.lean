module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AltExtension
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! R1: the metric contraction of `star2to3 a` agrees with `star3to2` of the exterior derivative
of `a`, for alternating `a`. Proved by substituting the canonical form `a = altTwo a`, then
`fin_cases` on the two free indices plus full numeral expansion. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

private theorem hodgeStarRule_one_i0 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (j : Fin 5) :
    contractionThree (star2to3 a) 0 j = star3to2 (exteriorTwo a) 0 j := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases j <;>
    simp [contractionThree, star2to3, star3to2, exteriorTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_one_i1 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (j : Fin 5) :
    contractionThree (star2to3 a) 1 j = star3to2 (exteriorTwo a) 1 j := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases j <;>
    simp [contractionThree, star2to3, star3to2, exteriorTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_one_i2 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (j : Fin 5) :
    contractionThree (star2to3 a) 2 j = star3to2 (exteriorTwo a) 2 j := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases j <;>
    simp [contractionThree, star2to3, star3to2, exteriorTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_one_i3 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (j : Fin 5) :
    contractionThree (star2to3 a) 3 j = star3to2 (exteriorTwo a) 3 j := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases j <;>
    simp [contractionThree, star2to3, star3to2, exteriorTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_one_i4 (a : TwoCoordinates) (ha : IsAlternatingTwo a) (j : Fin 5) :
    contractionThree (star2to3 a) 4 j = star3to2 (exteriorTwo a) 4 j := by
  rw [altTwo_eq_of_alternating ha]
  fin_cases j <;>
    simp [contractionThree, star2to3, star3to2, exteriorTwo, altTwo,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

theorem hodgeStarRule_one (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    contractionThree (star2to3 a) = star3to2 (exteriorTwo a) := by
  funext i j
  fin_cases i
  · exact hodgeStarRule_one_i0 a ha j
  · exact hodgeStarRule_one_i1 a ha j
  · exact hodgeStarRule_one_i2 a ha j
  · exact hodgeStarRule_one_i3 a ha j
  · exact hodgeStarRule_one_i4 a ha j

end TernaryPeriodPolynomials.Argument.Coercivity
