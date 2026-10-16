module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Approximation
public import TernaryPeriodPolynomials.DifferentialForm.WeightedConvergence
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Error

@[expose] public section

/-! True local metric-square convergence of the actual compact chart mollifier. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff

theorem mollifiedChartRaw_weighted_tendsto (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    Tendsto (fun c : ℝ => ∫ x, weightedSquare n k
      (fun y => mollifiedChartRaw n k S χ η c w y - η y • cutoffChartRaw n k S χ w y) x)
      atTop (nhds 0) := by
  let f := mollifiedChartError n k S χ η
  have hs (c : ℝ) : tsupport (f c w) ⊆ tsupport η := tsupport_mollifiedChartError n k S χ η c w
  have hw : ∀ᶠ c : ℝ in atTop, ContDiff ℝ ∞ (f c w) ∧ HasCompactSupport (f c w) ∧ tsupport (f c w) ⊆ tsupport η := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact ⟨contDiff_mollifiedChartError n k S χ η c hc.ne' hχ hsχ hη w,
      hcη.of_isClosed_subset (isClosed_tsupport _) (hs c),hs c⟩
  have ht : Tendsto (fun c : ℝ => ∫ x, ‖f c w x‖^2) atTop (nhds 0) := by
    simpa only [f, mollifiedChartError_apply] using
      mollifiedChartRaw_square_tendsto n k S χ η hχ hcχ hsχ hη.continuous hcη w
  have h := compact_weighted_square_tendsto n k (tsupport η) hcη
    (hsη.trans (quotientChart_target_subset S)) (fun c => f c w) hw ht
  simpa only [f, show ∀ c, mollifiedChartError n k S χ η c w =
      (fun y => mollifiedChartRaw n k S χ η c w y - η y • cutoffChartRaw n k S χ w y)
      from fun c => funext (mollifiedChartError_apply n k S χ η c w)] using h

end TernaryPoly.PolynomialFormCoordinates
