module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.RegularizerBound
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.BoundedExtension

@[expose] public section


/-! Actual bounded chart smoothing on the literal polynomial-form Hilbert completion. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
  SymmetricSpaceRiemannian
open scoped ContDiff SymmetricSpaceRiemannian

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)

def coreChartRegularizer (c : ℝ) (hc : 0 < c) : Core n k →ₗ[ℝ] Core n k :=
  (chartRegularizer n k S χ η c hc.ne' hχ hcχ hsχ hη hcη hsη).comp
    (CompactSupportForm (deckRepresentation n) univ k).subtype

/-- One bound works at every positive scale. -/
def chartRegularizerConstant : ℝ :=
  (exists_chart_regularizer_bound n k S χ η hχ hcχ hsχ hη hcη hsη).choose

theorem chartRegularizerConstant_nonneg :
    0 ≤ chartRegularizerConstant n k S χ η hχ hcχ hsχ hη hcη hsη :=
  (exists_chart_regularizer_bound n k S χ η hχ hcχ hsχ hη hcη hsη).choose_spec.1

theorem coreChartRegularizer_bound (c : ℝ) (hc : 0 < c) (w : Core n k) :
    ‖inclusion n k (coreChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)‖ ≤
      chartRegularizerConstant n k S χ η hχ hcχ hsχ hη hcη hsη * ‖inclusion n k w‖ :=
  (exists_chart_regularizer_bound n k S χ η hχ hcχ hsχ hη hcη hsη).choose_spec.2 c hc w

/-- Genuine bounded extension of the compact chart convolution to the actual L2 space. -/
def hilbertChartRegularizer (c : ℝ) (hc : 0 < c) : Hilbert n k →L[ℝ] Hilbert n k :=
  CompactPairingCompletion.boundedExtension orbitVolume (pairingData n k)
    (coreChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (chartRegularizerConstant n k S χ η hχ hcχ hsχ hη hcη hsη)
    (coreChartRegularizer_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc)

theorem hilbertChartRegularizer_inclusion (c : ℝ) (hc : 0 < c) (w : Core n k) :
    hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc (inclusion n k w) =
      inclusion n k (chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val) :=
  CompactPairingCompletion.boundedExtension_inclusion orbitVolume (pairingData n k)
    (coreChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (chartRegularizerConstant n k S χ η hχ hcχ hsχ hη hcη hsη)
    (coreChartRegularizer_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc) w

end TernaryPoly.PolynomialFormCoordinates
