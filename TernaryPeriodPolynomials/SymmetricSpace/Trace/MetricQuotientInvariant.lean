module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricInvariant
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldAtlas

@[expose] public section

/-! The genuine arithmetic quotient atlas preserves the positive metric on every overlap. -/
namespace TernaryPoly.SymmetricSpaceTraceMetric

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold
open scoped ContDiff Matrix.Norms.Elementwise

/-- The actual quotient-chart transition derivative preserves the same metric formula. -/
theorem coordinatePair_quotientChart_invariant (S T : Space) (x : Coordinates)
    (hx : x ∈ ((quotientChart S).symm.trans (quotientChart T)).source) (v w : Coordinates) :
    coordinatePair (((quotientChart S).symm.trans (quotientChart T)) x)
      (fderiv ℝ ((quotientChart S).symm.trans (quotientChart T)) x v)
      (fderiv ℝ ((quotientChart S).symm.trans (quotientChart T)) x w) =
      coordinatePair x v w := by
  obtain ⟨g, hg⟩ := quotientChart_transition_eventually S T x hx
  rw [hg.fderiv_eq, hg.eq_of_nhds]
  exact coordinatePair_fderiv_invariant
    (SymmetricSpaceArithmeticProper.realIntegral (deckInclusion g)) x
    (quotientChart_target_subset S hx.1) v w

/-- Invariance holds for every pair of charts in the actual quotient atlas. -/
theorem coordinatePair_atlas_invariant
    (e e' : OpenPartialHomeomorph OrbitSpace Coordinates)
    (he : e ∈ atlas Coordinates OrbitSpace) (he' : e' ∈ atlas Coordinates OrbitSpace)
    (x : Coordinates) (hx : x ∈ (e.symm.trans e').source) (v w : Coordinates) :
    coordinatePair ((e.symm.trans e') x)
      (fderiv ℝ (e.symm.trans e') x v) (fderiv ℝ (e.symm.trans e') x w) =
      coordinatePair x v w := by
  obtain ⟨S, rfl⟩ := he
  obtain ⟨T, rfl⟩ := he'
  exact coordinatePair_quotientChart_invariant S T x hx v w

end TernaryPoly.SymmetricSpaceTraceMetric
