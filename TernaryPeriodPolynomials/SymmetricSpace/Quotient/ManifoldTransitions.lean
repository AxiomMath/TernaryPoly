module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldLifts
public import TernaryPeriodPolynomials.SymmetricSpace.SymmetricSpaceChartOrientationConsumer

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientManifold
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open Topology Set
open scoped ContDiff

/-- Every actual covering-lift atlas transition is smooth on its full overlap domain. -/
theorem quotientChart_transition_contDiffOn (S T : Space) :
    ContDiffOn ℝ ∞ ((quotientChart S).symm.trans (quotientChart T))
      ((quotientChart S).symm.trans (quotientChart T)).source := by
  intro x hx
  obtain ⟨g,hg⟩ := quotientChart_transition_eventually S T x hx
  have hpos : x∈positiveCoordinates := quotientChart_target_subset S hx.1
  have h := (contDiffOn_coordinateAction
    (SymmetricSpaceArithmeticProper.realIntegral (deckInclusion g))).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hpos)
  exact (h.congr_of_eventuallyEq hg).contDiffWithinAt

/-- Each genuine overlap has positive derivative determinant in the literal five coordinates. -/
theorem quotientChart_transition_det_pos (S T : Space) (x : Coordinates)
    (hx : x∈((quotientChart S).symm.trans (quotientChart T)).source) :
    0 < LinearMap.det
      (fderiv ℝ ((quotientChart S).symm.trans (quotientChart T)) x).toLinearMap := by
  obtain ⟨g,hg⟩ := quotientChart_transition_eventually S T x hx
  rw [hg.fderiv_eq]
  exact SymmetricSpaceChartOrientation.coordinateAction_fderiv_det_pos
    (SymmetricSpaceArithmeticProper.realIntegral (deckInclusion g)) x
      (quotientChart_target_subset S hx.1)

end TernaryPoly.SymmetricSpaceQuotientManifold
