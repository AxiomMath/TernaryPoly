module

public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartDerivative
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartCodifferential
public import TernaryPeriodPolynomials.Analysis.DenseRegularizerApproximation

@[expose] public section

/-! Fixed-scale genuine chart regularizations admit one simultaneous compact graph approximation. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff Topology

theorem hilbertChartRegularizer_simultaneous_approximation (n k : ℕ) (S : Space)
    (χ η : Coordinates → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : 0 < c) (x : Hilbert n (k+1)) :
    ∃ u : ℕ → Core n (k+1),
      Tendsto (fun j => inclusion n (k+1) (u j)) atTop
        (𝓝 (hilbertChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc x)) ∧
      Tendsto (fun j => inclusion n (k+2)
        (compactDifferential (deckRepresentation n) isOpen_univ (k+1) (u j))) atTop
        (𝓝 (hilbertChartDifferential n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc x)) ∧
      Tendsto (fun j => inclusion n k (compactAdjoint n k (u j))) atTop
        (𝓝 (hilbertChartCodifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc x)) :=
  DenseRegularizerApproximation.exists_simultaneous_sequence
    (inclusion n (k+1)) (inclusion_dense n (k+1))
    (coreChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (fun w => inclusion n (k+2) (compactDifferential (deckRepresentation n) isOpen_univ (k+1) w))
    (fun w => inclusion n k (compactAdjoint n k w))
    (hilbertChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartDifferential n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartCodifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartRegularizer_inclusion n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartDifferential_inclusion n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartCodifferential_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη c hc) x

end TernaryPoly.PolynomialFormCoordinates
