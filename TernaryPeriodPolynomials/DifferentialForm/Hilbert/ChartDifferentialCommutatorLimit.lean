module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential.CommutatorStrong
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartDifferentialCommutator
public import TernaryPeriodPolynomials.Analysis.Bounded.CompletionStrongLimit

@[expose] public section


/-! The uniformly bounded literal differential chart commutators converge on the full Hilbert space. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert SymmetricSpaceRiemannian
open scoped ContDiff SymmetricSpaceRiemannian

theorem exists_hilbertChartDifferentialCommutatorLimit (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target) :
    ∃ L : Hilbert n k →L[ℝ] Hilbert n (k+1),
      (∀ w : Core n k, L (inclusion n k w) =
        inclusion n (k+1) (coreChartDifferentialLimit n k S χ η hχ hη hcη hsη w)) ∧
      (∀ x : Hilbert n k, Tendsto (fun j : ℕ =>
        hilbertChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) x)
        atTop (nhds (L x))) := by
  let T (j : ℕ) := hilbertChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη
    ((j:ℝ)+1) (by positivity)
  let f (v : CompactPairingCompletion.Space orbitVolume (pairingData n k)) :=
    inclusion n (k+1) (coreChartDifferentialLimit n k S χ η hχ hη hcη hsη v)
  have hT (j : ℕ) : ‖T j‖ ≤ chartDifferentialCommutatorConstant n k S χ η hχ hcχ hsχ hη hcη hsη :=
    hilbertChartDifferentialCommutator_opNorm_le n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity)
  have hf (v : CompactPairingCompletion.Space orbitVolume (pairingData n k)) :
      Tendsto (fun j => T j (v : UniformSpace.Completion _)) atTop (nhds (f v)) := by
    change Tendsto (fun j => T j (inclusion n k v)) atTop (nhds (f v))
    have heq (j : ℕ) := hilbertChartDifferentialCommutator_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη
      ((j:ℝ)+1) (by positivity) v
    exact (coreChartDifferentialCommutator_tendsto n k S χ η hχ hcχ hsχ hη hcη hsη v).congr
      (fun j => (heq j).symm)
  exact BoundedCompletionStrongLimit.exists_strong_limit T _
    (chartDifferentialCommutatorConstant_nonneg n k S χ η hχ hcχ hsχ hη hcη hsη) hT f hf

end TernaryPoly.PolynomialFormCoordinates
