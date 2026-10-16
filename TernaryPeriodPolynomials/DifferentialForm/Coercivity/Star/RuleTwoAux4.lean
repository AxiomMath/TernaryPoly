module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AltExtension
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! R2, first index fixed to `4`. See `StarRuleTwoAux0.lean` for the rationale of the split. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

private theorem hodgeStarRule_two_aux4_j0 (b : ThreeCoordinates) (hb : IsAlternatingThree b) (k : Fin 5) :
    exteriorTwo (star3to2 b) 4 0 k = star2to3 (contractionThree b) 4 0 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;>
    simp [exteriorTwo, star3to2, star2to3, contractionThree, altThree,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_two_aux4_j1 (b : ThreeCoordinates) (hb : IsAlternatingThree b) (k : Fin 5) :
    exteriorTwo (star3to2 b) 4 1 k = star2to3 (contractionThree b) 4 1 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;>
    simp [exteriorTwo, star3to2, star2to3, contractionThree, altThree,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_two_aux4_j2 (b : ThreeCoordinates) (hb : IsAlternatingThree b) (k : Fin 5) :
    exteriorTwo (star3to2 b) 4 2 k = star2to3 (contractionThree b) 4 2 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;>
    simp [exteriorTwo, star3to2, star2to3, contractionThree, altThree,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_two_aux4_j3 (b : ThreeCoordinates) (hb : IsAlternatingThree b) (k : Fin 5) :
    exteriorTwo (star3to2 b) 4 3 k = star2to3 (contractionThree b) 4 3 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;>
    simp [exteriorTwo, star3to2, star2to3, contractionThree, altThree,
      Fin.sum_univ_five, map_add, map_neg] <;>
    module

private theorem hodgeStarRule_two_aux4_j4 (b : ThreeCoordinates) (hb : IsAlternatingThree b) (k : Fin 5) :
    exteriorTwo (star3to2 b) 4 4 k = star2to3 (contractionThree b) 4 4 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;>
    simp [exteriorTwo, star3to2, star2to3, contractionThree, altThree,
      Fin.sum_univ_five, map_add, map_neg]

theorem hodgeStarRule_two_aux4 (b : ThreeCoordinates) (hb : IsAlternatingThree b) (j k : Fin 5) :
    exteriorTwo (star3to2 b) 4 j k = star2to3 (contractionThree b) 4 j k := by
  fin_cases j
  · exact hodgeStarRule_two_aux4_j0 b hb k
  · exact hodgeStarRule_two_aux4_j1 b hb k
  · exact hodgeStarRule_two_aux4_j2 b hb k
  · exact hodgeStarRule_two_aux4_j3 b hb k
  · exact hodgeStarRule_two_aux4_j4 b hb k

end TernaryPeriodPolynomials.Argument.Coercivity
