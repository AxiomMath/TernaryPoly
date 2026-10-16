module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.OrbitCoverMeasure

@[expose] public section


open MeasureTheory
open scoped Pointwise ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem fundamental_domain_lintegral_le_orbit_cover
    {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
    [MeasurableConstSMul G X] [Countable G] {measure : Measure X}
    [SMulInvariantMeasure G X measure] {domain cover : Set X}
    (fundamental : IsFundamentalDomain G domain measure)
    (covering : (⋃ element : G, element • cover) = Set.univ)
    (function : X → ℝ≥0∞) (invariant : ∀ element : G, ∀ point, function (element • point) = function point) :
    (∫⁻ point in domain, function point ∂measure) ≤ ∫⁻ point in cover, function point ∂measure := by
  rw [fundamental.setLIntegral_eq_tsum' function cover]
  simp only [invariant]
  calc
    _ = ∫⁻ point in ⋃ element : G, element • cover ∩ domain, function point ∂measure := by
      rw [← Set.iUnion_inter, covering, Set.univ_inter]
    _ ≤ ∑' element : G, ∫⁻ point in element • cover ∩ domain, function point ∂measure := lintegral_iUnion_le _ _

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
