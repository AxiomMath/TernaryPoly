module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Codifferential.CommutatorNorm
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.TargetExtensionNorm

@[expose] public section


/-! The genuine chart codifferential commutator extends uniformly to arbitrary Hilbert inputs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert SymmetricSpaceRiemannian
open scoped ContDiff SymmetricSpaceRiemannian

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)

def chartCodifferentialCommutatorConstant : ℝ :=
  (exists_codifferentialCommutator_norm_bound n k S χ η hχ hcχ hsχ hη hcη hsη).choose

theorem chartCodifferentialCommutatorConstant_nonneg :
    0 ≤ chartCodifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη :=
  (exists_codifferentialCommutator_norm_bound n k S χ η hχ hcχ hsχ hη hcη hsη).choose_spec.1

theorem coreChartCodifferentialCommutator_bound (c : ℝ) (hc : 0 < c) (w : Core n (k+1)) :
    ‖inclusion n k (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)‖ ≤
      chartCodifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη * ‖inclusion n (k+1) w‖ :=
  (exists_codifferentialCommutator_norm_bound n k S χ η hχ hcχ hsχ hη hcη hsη).choose_spec.2 c hc w

def hilbertChartCodifferentialCommutator (c : ℝ) (hc : 0 < c) : Hilbert n (k+1) →L[ℝ] Hilbert n k :=
  CompactPairingCompletion.boundedTargetExtension orbitVolume (pairingData n (k+1))
    ((inclusion n k).comp (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc))
    (chartCodifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη)
    (coreChartCodifferentialCommutator_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc)

theorem hilbertChartCodifferentialCommutator_inclusion (c : ℝ) (hc : 0 < c) (w : Core n (k+1)) :
    hilbertChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc (inclusion n (k+1) w) =
      inclusion n k (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w) :=
  CompactPairingCompletion.boundedTargetExtension_inclusion orbitVolume (pairingData n (k+1))
    ((inclusion n k).comp (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc))
    (chartCodifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη)
    (coreChartCodifferentialCommutator_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc) w

theorem hilbertChartCodifferentialCommutator_bound (c : ℝ) (hc : 0 < c) (w : Hilbert n (k+1)) :
    ‖hilbertChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w‖ ≤
      chartCodifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη * ‖w‖ :=
  CompactPairingCompletion.boundedTargetExtension_bound orbitVolume (pairingData n (k+1))
    ((inclusion n k).comp (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc))
    (chartCodifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη)
    (coreChartCodifferentialCommutator_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc) w

theorem hilbertChartCodifferentialCommutator_opNorm_le (c : ℝ) (hc : 0 < c) :
    ‖hilbertChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc‖ ≤
      chartCodifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη :=
  ContinuousLinearMap.opNorm_le_bound _
    (chartCodifferentialCommutatorConstant_nonneg n k S χ η hχ hcχ hsχ hη hcη hsη)
    (hilbertChartCodifferentialCommutator_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc)

end TernaryPoly.PolynomialFormCoordinates
