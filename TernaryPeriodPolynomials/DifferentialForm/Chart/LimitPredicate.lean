module

public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartLimit

@[expose] public section


/-! A named predicate for the literal strong convergence of actual Hilbert chart regularizers. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter PolynomialFormHilbert SymmetricSpaceCharts SymmetricSpaceCovering
  SymmetricSpacePositive
open scoped ContDiff Topology

def HasStrongHilbertChartLimit (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target)
    (L : Hilbert n k →L[ℝ] Hilbert n k) : Prop :=
  ∀ x : Hilbert n k, Tendsto (fun j : ℕ =>
    hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη
      ((j : ℝ) + 1) (by positivity) x) atTop (𝓝 (L x))

end TernaryPoly.PolynomialFormCoordinates
