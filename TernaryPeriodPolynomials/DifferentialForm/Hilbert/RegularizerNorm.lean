module

public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Regularizer
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.ExtensionNorm

@[expose] public section


/-! The true Hilbert chart regularizers share one scale-independent operator norm bound. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
  SymmetricSpaceRiemannian
open scoped ContDiff SymmetricSpaceRiemannian

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)

theorem hilbertChartRegularizer_bound (c : ℝ) (hc : 0 < c) (w : Hilbert n k) :
    ‖hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc w‖ ≤
      chartRegularizerConstant n k S χ η hχ hcχ hsχ hη hcη hsη * ‖w‖ :=
  CompactPairingCompletion.boundedExtension_bound orbitVolume (pairingData n k)
    (coreChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (chartRegularizerConstant n k S χ η hχ hcχ hsχ hη hcη hsη)
    (coreChartRegularizer_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc) w

theorem hilbertChartRegularizer_opNorm_le (c : ℝ) (hc : 0 < c) :
    ‖hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc‖ ≤
      chartRegularizerConstant n k S χ η hχ hcχ hsχ hη hcη hsη :=
  ContinuousLinearMap.opNorm_le_bound _
    (chartRegularizerConstant_nonneg n k S χ η hχ hcχ hsχ hη hcη hsη)
    (hilbertChartRegularizer_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc)

end TernaryPoly.PolynomialFormCoordinates
