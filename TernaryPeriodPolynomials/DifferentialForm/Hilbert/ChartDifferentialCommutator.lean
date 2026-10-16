module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential.CommutatorNorm
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.TargetExtensionNorm

@[expose] public section


/-! The genuine chart differential commutator extends uniformly to arbitrary Hilbert inputs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert SymmetricSpaceRiemannian
open scoped ContDiff SymmetricSpaceRiemannian

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)

def chartDifferentialCommutatorConstant : ℝ :=
  (exists_differentialCommutator_norm_bound n k S χ η hχ hcχ hsχ hη hcη hsη).choose

theorem chartDifferentialCommutatorConstant_nonneg :
    0 ≤ chartDifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη :=
  (exists_differentialCommutator_norm_bound n k S χ η hχ hcχ hsχ hη hcη hsη).choose_spec.1

theorem coreChartDifferentialCommutator_bound (c : ℝ) (hc : 0 < c) (w : Core n k) :
    ‖inclusion n (k+1) (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)‖ ≤
      chartDifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη * ‖inclusion n k w‖ :=
  (exists_differentialCommutator_norm_bound n k S χ η hχ hcχ hsχ hη hcη hsη).choose_spec.2 c hc w

def hilbertChartDifferentialCommutator (c : ℝ) (hc : 0 < c) : Hilbert n k →L[ℝ] Hilbert n (k+1) :=
  CompactPairingCompletion.boundedTargetExtension orbitVolume (pairingData n k)
    ((inclusion n (k+1)).comp (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc))
    (chartDifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη)
    (coreChartDifferentialCommutator_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc)

theorem hilbertChartDifferentialCommutator_inclusion (c : ℝ) (hc : 0 < c) (w : Core n k) :
    hilbertChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc (inclusion n k w) =
      inclusion n (k+1) (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w) :=
  CompactPairingCompletion.boundedTargetExtension_inclusion orbitVolume (pairingData n k)
    ((inclusion n (k+1)).comp (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc))
    (chartDifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη)
    (coreChartDifferentialCommutator_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc) w

theorem hilbertChartDifferentialCommutator_bound (c : ℝ) (hc : 0 < c) (w : Hilbert n k) :
    ‖hilbertChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w‖ ≤
      chartDifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη * ‖w‖ :=
  CompactPairingCompletion.boundedTargetExtension_bound orbitVolume (pairingData n k)
    ((inclusion n (k+1)).comp (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc))
    (chartDifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη)
    (coreChartDifferentialCommutator_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc) w

theorem hilbertChartDifferentialCommutator_opNorm_le (c : ℝ) (hc : 0 < c) :
    ‖hilbertChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc‖ ≤
      chartDifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη :=
  ContinuousLinearMap.opNorm_le_bound _
    (chartDifferentialCommutatorConstant_nonneg n k S χ η hχ hcχ hsχ hη hcη hsη)
    (hilbertChartDifferentialCommutator_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc)

end TernaryPoly.PolynomialFormCoordinates
