module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Codifferential.CommutatorStrong
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartCodifferentialCommutator
public import TernaryPeriodPolynomials.Analysis.Bounded.CompletionStrongLimit

@[expose] public section

/-! Actual strong convergence of codifferential chart commutators on the entire Hilbert completion. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert SymmetricSpaceRiemannian
open scoped ContDiff SymmetricSpaceRiemannian

theorem exists_hilbertChartCodifferentialCommutatorLimit (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target) :
    ∃ L : Hilbert n (k+1) →L[ℝ] Hilbert n k,
      (∀ w : Core n (k+1), L (inclusion n (k+1) w) = inclusion n k (coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w)) ∧
      (∀ x : Hilbert n (k+1), Tendsto (fun j : ℕ =>
        hilbertChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) x)
        atTop (nhds (L x))) := by
  let T (j : ℕ) := hilbertChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity)
  let f (v : CompactPairingCompletion.Space orbitVolume (pairingData n (k+1))) :=
    inclusion n k (coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη v)
  have hT (j : ℕ) : ‖T j‖ ≤ chartCodifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη :=
    hilbertChartCodifferentialCommutator_opNorm_le n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity)
  have hf (v : CompactPairingCompletion.Space orbitVolume (pairingData n (k+1))) :
      Tendsto (fun j => T j (v : UniformSpace.Completion _)) atTop (nhds (f v)) := by
    change Tendsto (fun j => T j (inclusion n (k+1) v)) atTop (nhds (f v))
    have heq (j : ℕ) := hilbertChartCodifferentialCommutator_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη
      ((j : ℝ) + 1) (by positivity) v
    have hlim := coreChartCodifferentialCommutator_tendsto n k S χ η hχ hcχ hsχ hη hcη hsη v
    exact hlim.congr (fun j => (heq j).symm)
  exact BoundedCompletionStrongLimit.exists_strong_limit T _
    (chartCodifferentialCommutatorConstant_nonneg n k S χ η hχ hcχ hsχ hη hcη hsη) hT f hf

end TernaryPoly.PolynomialFormCoordinates
