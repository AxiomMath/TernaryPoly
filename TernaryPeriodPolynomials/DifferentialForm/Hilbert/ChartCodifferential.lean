module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.AdjointNorm
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Regularizer
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.BoundedTarget
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section


/-! Actual fixed-scale compact codifferential extends boundedly to arbitrary Hilbert inputs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert SymmetricSpaceRiemannian
open scoped ContDiff SymmetricSpaceRiemannian

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : 0 < c)

def chartCodifferentialCore : Core n (k+1) →ₗ[ℝ] Hilbert n k :=
  (inclusion n k).comp ((compactAdjoint n k).comp
    (coreChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc))

theorem chartCodifferentialCore_apply (w : Core n (k+1)) :
    chartCodifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc w =
      inclusion n k (compactAdjoint n k (chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη w.val)) := rfl

theorem exists_chartCodifferentialCore_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Core n (k+1),
      ‖chartCodifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc w‖ ≤ C * ‖inclusion n (k+1) w‖ := by
  have H := exists_chart_adjoint_square_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc.ne'
  let C : ℝ := H.choose
  have hC : 0 ≤ C := H.choose_spec.1
  refine ⟨Real.sqrt C,Real.sqrt_nonneg C,fun w => ?_⟩
  have hh : ‖chartCodifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc w‖^2 ≤
      C * ‖inclusion n (k+1) w‖^2 :=
    (congrArg (fun z : Hilbert n k => ‖z‖^2)
      (chartCodifferentialCore_apply n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)).le.trans
      (H.choose_spec.2 w)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (inclusion n (k+1) w)))).mp
  simpa only [mul_pow, Real.sq_sqrt hC] using hh

def hilbertChartCodifferential : Hilbert n (k+1) →L[ℝ] Hilbert n k :=
  CompactPairingCompletion.boundedTargetExtension orbitVolume (pairingData n (k+1))
    (chartCodifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (exists_chartCodifferentialCore_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc).choose
    (exists_chartCodifferentialCore_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc).choose_spec.2

theorem hilbertChartCodifferential_inclusion (w : Core n (k+1)) :
    hilbertChartCodifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc (inclusion n (k+1) w) =
      inclusion n k (compactAdjoint n k (chartMollifier n (k+1) S χ η c hc.ne' hχ hsχ hη hcη hsη w.val)) :=
  CompactPairingCompletion.boundedTargetExtension_inclusion orbitVolume (pairingData n (k+1))
    (chartCodifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (exists_chartCodifferentialCore_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc).choose
    (exists_chartCodifferentialCore_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc).choose_spec.2 w

end TernaryPoly.PolynomialFormCoordinates
