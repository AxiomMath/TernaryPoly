module

public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartLimit

@[expose] public section

/-! Any bounded operator with the actual compact cutoff values is the chart strong limit. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff Topology

theorem hilbertChartRegularizer_tendsto_of_core (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (L : Hilbert n k →L[ℝ] Hilbert n k)
    (hL : ∀ w : Core n k, L (inclusion n k w) =
      inclusion n k (doubleChartCutoff n k S χ η hχ hη hcη hsη w.val)) (x : Hilbert n k) :
    Tendsto (fun j : ℕ => hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη
      ((j:ℝ)+1) (by positivity) x) atTop (𝓝 (L x)) := by
  have H := exists_hilbertChartLimit n k S χ η hχ hcχ hsχ hη hcη hsη
  let M := H.choose
  have he : M x = L x := by
    refine (inclusion_dense n k).induction_on x (isClosed_eq M.continuous L.continuous) ?_
    intro w
    exact (H.choose_spec.1 w).trans (hL w).symm
  exact (H.choose_spec.2 x).mono_right (le_of_eq (congrArg nhds he))

end TernaryPoly.PolynomialFormCoordinates
