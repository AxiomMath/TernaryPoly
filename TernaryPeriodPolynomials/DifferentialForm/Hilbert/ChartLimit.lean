module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.StrongConvergence
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.RegularizerNorm
public import TernaryPeriodPolynomials.Analysis.Bounded.CompletionStrongLimit

@[expose] public section

/-! Actual strong convergence of chart regularizers on the entire Hilbert completion. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert SymmetricSpaceRiemannian
open scoped ContDiff SymmetricSpaceRiemannian

theorem exists_hilbertChartLimit (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target) :
    ∃ L : Hilbert n k →L[ℝ] Hilbert n k,
      (∀ w : Core n k, L (inclusion n k w) = inclusion n k (doubleChartCutoff n k S χ η hχ hη hcη hsη w.val)) ∧
      (∀ x : Hilbert n k, Tendsto (fun j : ℕ =>
        hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) x)
        atTop (nhds (L x))) := by
  let T (j : ℕ) := hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity)
  let f (v : CompactPairingCompletion.Space orbitVolume (pairingData n k)) :=
    inclusion n k (doubleChartCutoff n k S χ η hχ hη hcη hsη v.val)
  have hT (j : ℕ) : ‖T j‖ ≤ chartRegularizerConstant n k S χ η hχ hcχ hsχ hη hcη hsη :=
    hilbertChartRegularizer_opNorm_le n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity)
  have hf (v : CompactPairingCompletion.Space orbitVolume (pairingData n k)) :
      Tendsto (fun j => T j (v : UniformSpace.Completion _)) atTop (nhds (f v)) := by
    change Tendsto (fun j => T j (inclusion n k v)) atTop (nhds (f v))
    have heq (j : ℕ) := hilbertChartRegularizer_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη
      ((j : ℝ) + 1) (by positivity) v
    have hlim := chartMollifier_inclusion_tendsto n k S χ η hχ hcχ hsχ hη hcη hsη v.val
    exact hlim.congr (fun j => (heq j).symm)
  exact BoundedCompletionStrongLimit.exists_strong_limit T _
    (chartRegularizerConstant_nonneg n k S χ η hχ hcχ hsχ hη hcη hsη) hT f hf

end TernaryPoly.PolynomialFormCoordinates
