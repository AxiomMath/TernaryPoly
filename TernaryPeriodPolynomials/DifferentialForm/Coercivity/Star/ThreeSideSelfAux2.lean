module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AltExtension
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! First-index-2 slice of the three-sided involution helper `star2to3 (star3to2 b) = (1/96) • b`
(needed for INVOLUTION; see `StarThreeSideSelf.lean`), split by second index `j` as in
`StarThreeSideSelfAux0.lean`. The `j = 2` sub-case is diagonal (`i = j`), so `altThree` already
forces it to zero and `simp` alone closes it. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star2to3_star3to2_self_aux2_0 (b : ThreeCoordinates) (hb : IsAlternatingThree b)
    (k : Fin 5) : star2to3 (star3to2 b) 2 0 k = (1/96 : ℝ) • b 2 0 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;> simp only [star2to3, Fin.sum_univ_five]
  all_goals simp
  all_goals simp [star3to2, altThree, Fin.sum_univ_five, tangentWeight]
  all_goals module

theorem star2to3_star3to2_self_aux2_1 (b : ThreeCoordinates) (hb : IsAlternatingThree b)
    (k : Fin 5) : star2to3 (star3to2 b) 2 1 k = (1/96 : ℝ) • b 2 1 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;> simp only [star2to3, Fin.sum_univ_five]
  all_goals simp
  all_goals simp [star3to2, altThree, Fin.sum_univ_five, tangentWeight]
  all_goals module

theorem star2to3_star3to2_self_aux2_2 (b : ThreeCoordinates) (hb : IsAlternatingThree b)
    (k : Fin 5) : star2to3 (star3to2 b) 2 2 k = (1/96 : ℝ) • b 2 2 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;> simp [star2to3, altThree]

theorem star2to3_star3to2_self_aux2_3 (b : ThreeCoordinates) (hb : IsAlternatingThree b)
    (k : Fin 5) : star2to3 (star3to2 b) 2 3 k = (1/96 : ℝ) • b 2 3 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;> simp only [star2to3, Fin.sum_univ_five]
  all_goals simp
  all_goals simp [star3to2, altThree, Fin.sum_univ_five, tangentWeight]
  all_goals module

theorem star2to3_star3to2_self_aux2_4 (b : ThreeCoordinates) (hb : IsAlternatingThree b)
    (k : Fin 5) : star2to3 (star3to2 b) 2 4 k = (1/96 : ℝ) • b 2 4 k := by
  rw [altThree_eq_of_alternating hb]
  fin_cases k <;> simp only [star2to3, Fin.sum_univ_five]
  all_goals simp
  all_goals simp [star3to2, altThree, Fin.sum_univ_five, tangentWeight]
  all_goals module

theorem star2to3_star3to2_self_aux2 (b : ThreeCoordinates) (hb : IsAlternatingThree b)
    (j k : Fin 5) : star2to3 (star3to2 b) 2 j k = (1/96 : ℝ) • b 2 j k := by
  fin_cases j
  · exact star2to3_star3to2_self_aux2_0 b hb k
  · exact star2to3_star3to2_self_aux2_1 b hb k
  · exact star2to3_star3to2_self_aux2_2 b hb k
  · exact star2to3_star3to2_self_aux2_3 b hb k
  · exact star2to3_star3to2_self_aux2_4 b hb k

end TernaryPeriodPolynomials.Argument.Coercivity
