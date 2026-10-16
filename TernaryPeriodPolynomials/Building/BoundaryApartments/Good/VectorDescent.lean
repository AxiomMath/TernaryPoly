module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.TetrahedronRefinement

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

def goodVectorDescentData : TetrahedronDescentData NormalizedGoodVector ApartmentQuotient where
  height := goodTripleHeight
  initial := goodTripleInitial
  reduce := goodTripleReducer
  decrease := goodTripleReducer_decrease
  initial_relation := goodTripleInitial_relation
  refine_relation := goodTetrahedron_refine

def goodTripleValue : OrderedTriple NormalizedGoodVector → ApartmentQuotient :=
  descendedTripleValue goodVectorDescentData

theorem goodTripleValue_initial (triple : OrderedTriple NormalizedGoodVector)
    (small : goodTripleHeight triple ≤ 1) : goodTripleValue triple = goodTripleInitial triple :=
  descendedTripleValue_small goodVectorDescentData triple small

theorem goodTripleValue_relation (a b c d : NormalizedGoodVector) :
    goodTripleValue (b, c, d) - goodTripleValue (a, c, d) + goodTripleValue (a, b, d) -
      goodTripleValue (a, b, c) = 0 :=
  descendedTripleValue_relation goodVectorDescentData (a, b, c, d)

theorem goodTripleValue_zero (triple : OrderedTriple NormalizedGoodVector)
    (zero : goodTripleHeight triple = 0) : goodTripleValue triple = 0 := by
  rw [goodTripleValue_initial triple (by omega), goodTripleInitial_zero triple zero]

theorem goodTripleHeight_repeat (a b : NormalizedGoodVector) : goodTripleHeight (a, a, b) = 0 := by
  have determinant : (goodTripleMatrix (a, a, b)).det = 0 := by
    simp [goodTripleMatrix, vectorTripleMatrix, Matrix.det_fin_three]
  simp only [goodTripleHeight, determinant, Int.natAbs_zero]

theorem goodTripleValue_repeat_first (a b : NormalizedGoodVector) : goodTripleValue (a, a, b) = 0 :=
  goodTripleValue_zero _ (goodTripleHeight_repeat a b)

theorem goodTripleValue_repeat_last (a b : NormalizedGoodVector) : goodTripleValue (a, b, b) = 0 := by
  apply goodTripleValue_zero
  rw [← goodTripleHeight_cyclic a b b, goodTripleHeight_repeat]

theorem goodTripleValue_repeat_outer (a b : NormalizedGoodVector) : goodTripleValue (a, b, a) = 0 := by
  apply goodTripleValue_zero
  rw [goodTripleHeight_swap_last a a b, goodTripleHeight_repeat]

theorem goodTripleValue_swap (a b c : NormalizedGoodVector) :
    goodTripleValue (b, a, c) = -goodTripleValue (a, b, c) := by
  have relation := goodTripleValue_relation a b a c
  rw [goodTripleValue_repeat_first, goodTripleValue_repeat_outer, sub_zero, sub_zero] at relation
  exact eq_neg_of_add_eq_zero_left relation

theorem goodTripleValue_cyclic (a b c : NormalizedGoodVector) :
    goodTripleValue (b, c, a) = goodTripleValue (a, b, c) := by
  have relation := goodTripleValue_relation a b c a
  rw [goodTripleValue_repeat_outer, goodTripleValue_repeat_outer, sub_zero, add_zero] at relation
  exact sub_eq_zero.mp relation

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
