module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.DerivativeNorm
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Regularizer
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.BoundedTarget
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! The actual compact differential after chart smoothing extends boundedly to all Hilbert inputs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert SymmetricSpaceRiemannian
open scoped ContDiff SymmetricSpaceRiemannian

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : 0 < c)

def chartDifferentialCore : Core n k →ₗ[ℝ] Hilbert n (k+1) :=
  (inclusion n (k+1)).comp ((compactDifferential (deckRepresentation n) isOpen_univ k).comp
    (coreChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc))

theorem chartDifferentialCore_apply (w : Core n k) :
    chartDifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc w =
      inclusion n (k+1) (compactDifferential (deckRepresentation n) isOpen_univ k
        (chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val)) := rfl

theorem exists_chartDifferentialCore_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Core n k,
      ‖chartDifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc w‖ ≤ C * ‖inclusion n k w‖ := by
  have H := exists_chart_differential_square_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc.ne'
  let C : ℝ := H.choose
  have hC : 0 ≤ C := H.choose_spec.1
  refine ⟨Real.sqrt C,Real.sqrt_nonneg C,fun w => ?_⟩
  have hh : ‖chartDifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc w‖^2 ≤
      C * ‖inclusion n k w‖^2 := by
    exact (congrArg (fun z : Hilbert n (k+1) => ‖z‖^2)
      (chartDifferentialCore_apply n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)).le.trans
      (H.choose_spec.2 w)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (inclusion n k w)))).mp
  simpa only [mul_pow, Real.sq_sqrt hC] using hh

def hilbertChartDifferential : Hilbert n k →L[ℝ] Hilbert n (k+1) :=
  CompactPairingCompletion.boundedTargetExtension orbitVolume (pairingData n k)
    (chartDifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (exists_chartDifferentialCore_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc).choose
    (exists_chartDifferentialCore_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc).choose_spec.2

theorem hilbertChartDifferential_inclusion (w : Core n k) :
    hilbertChartDifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc (inclusion n k w) =
      inclusion n (k+1) (compactDifferential (deckRepresentation n) isOpen_univ k
        (chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val)) :=
  CompactPairingCompletion.boundedTargetExtension_inclusion orbitVolume (pairingData n k)
    (chartDifferentialCore n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (exists_chartDifferentialCore_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc).choose
    (exists_chartDifferentialCore_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc).choose_spec.2 w

end TernaryPoly.PolynomialFormCoordinates
