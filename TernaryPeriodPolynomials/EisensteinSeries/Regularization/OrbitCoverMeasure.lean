module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearReduction
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearQuotientMeasure

@[expose] public section


open Matrix MeasureTheory
open scoped Pointwise ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem fundamental_domain_measure_le_orbit_cover
    {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
    [MeasurableConstSMul G X] [Countable G] {measure : Measure X}
    [SMulInvariantMeasure G X measure] {domain cover : Set X}
    (fundamental : IsFundamentalDomain G domain measure)
    (covering : (⋃ element : G, element • cover) = Set.univ) :
    measure domain ≤ measure cover := by
  rw [fundamental.measure_eq_tsum cover]
  calc
    measure domain = measure (⋃ element : G, element • cover ∩ domain) := by
      rw [← Set.iUnion_inter, covering, Set.univ_inter]
    _ ≤ ∑' element : G, measure (element • cover ∩ domain) := measure_iUnion_le _

theorem integerSpecialLinearQuotientMeasure_le_reducedCover :
    integerSpecialLinearQuotientMeasure Set.univ ≤ realSpecialLinearHaar realSpecialLinearReducedCover := by
  rw [integerSpecialLinearQuotientMeasure_univ]
  exact fundamental_domain_measure_le_orbit_cover integerSpecialLinearDomain_fundamental
    realSpecialLinearReducedCover_iUnion

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
