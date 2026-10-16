module

public import TernaryPeriodPolynomials.DifferentialForm.Compact.ChartPartitionData
public import TernaryPeriodPolynomials.DifferentialForm.Chart.ScalarAgreement

@[expose] public section


/-! The scalar agreement of each actual compact chart partition term. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set PolynomialFormHilbert PolynomialCoefficientMetric PolynomialFormConnection
  SmoothLocalDeRham SmoothCoveringDeRham SmoothDeRhamGluing
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
open scoped ContDiff Manifold

theorem CompactChartPartitionData.core_agreement {K : Set OrbitSpace}
    (p : CompactChartPartitionData K) (n k : ℕ) (i : p.charts) (a : Core n k) :
    doubleChartCutoff n k i.val (p.cutoff i).inner (p.cutoff i).outer
      (p.cutoff i).inner_smooth (p.cutoff i).outer_smooth
      (p.cutoff i).outer_compact (p.cutoff i).outer_support a.val =
      coreScalarMultiply n k (p.scalar i) (p.smooth i) a := by
  let c := p.cutoff i
  apply Subtype.ext
  apply eq_of_globalChartRepresentative_eq (deckRepresentation n) i.val
  · exact quotientSupport_chartCutoff n k i.val (c.outer * c.inner) (c.outer_smooth.mul c.inner_smooth)
      c.outer_compact.mul_right (tsupport_mul_subset_left.trans c.outer_support) a.val
  · rw [coreScalarMultiply_val]
    exact (quotientSupport_scalarMultiply_subset_tsupport (p.scalar i)
      (p.smooth i).contMDiffOn a.val).trans (p.support i)
  · apply Form.ext
    intro x hx
    have hl := globalChartRepresentative_apply (deckRepresentation n) i.val
      (doubleChartCutoff n k i.val c.inner c.outer c.inner_smooth c.outer_smooth
        c.outer_compact c.outer_support a.val).val hx
    have hr := globalChartRepresentative_apply (deckRepresentation n) i.val
      (coreScalarMultiply n k (p.scalar i) (p.smooth i) a).val hx
    have hs : (c.outer * c.inner) x = p.scalar i (coordinateProjection x) :=
      (congrFun (p.outer_mul i) x).trans ((congrFun (p.inner_eq i) x).trans
        ((coordinateScalar_apply i.val (p.scalar i) hx).trans
          (congrArg (p.scalar i) (quotientChart_projection_coordinates i.val hx))))
    exact hl.trans ((chartCutoff_apply n k i.val (c.outer * c.inner)
      (c.outer_smooth.mul c.inner_smooth) c.outer_compact.mul_right
      (tsupport_mul_subset_left.trans c.outer_support) a.val hx).trans
        ((congrArg (fun t : ℝ => t • a.val.val.val x) hs).trans
          ((coreScalarMultiply_apply n k (p.scalar i) (p.smooth i) a x).symm.trans hr.symm)))

end TernaryPoly.PolynomialFormCoordinates
