module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Metric
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.ExtensionNorm

@[expose] public section


/-! Actual bounded scalar multiplication on the polynomial-form Hilbert completion. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set MeasureTheory PolynomialFormMetric PolynomialFormHilbert SymmetricSpaceCharts
  SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped ContDiff Manifold SymmetricSpaceRiemannian

variable (n k : ℕ) (χ : OrbitSpace → ℝ)
  (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (A : ℝ) (hA : 0 ≤ A)
  (hb : ∀ q, |χ q| ≤ A)

/-- Bounded extension of literal scalar multiplication on the actual compact core. -/
def scalarMultiplier : Hilbert n k →L[ℝ] Hilbert n k :=
  CompactPairingCompletion.boundedExtension orbitVolume (pairingData n k)
    (coreScalarMultiply n k χ hχ) A (coreScalarMultiply_bound n k χ hχ hA hb)

theorem scalarMultiplier_inclusion (a : Core n k) :
    scalarMultiplier n k χ hχ A hA hb (inclusion n k a) =
      inclusion n k (coreScalarMultiply n k χ hχ a) :=
  CompactPairingCompletion.boundedExtension_inclusion orbitVolume (pairingData n k)
    (coreScalarMultiply n k χ hχ) A (coreScalarMultiply_bound n k χ hχ hA hb) a

theorem scalarMultiplier_bound (a : Hilbert n k) :
    ‖scalarMultiplier n k χ hχ A hA hb a‖ ≤ A * ‖a‖ :=
  CompactPairingCompletion.boundedExtension_bound orbitVolume (pairingData n k)
    (coreScalarMultiply n k χ hχ) A (coreScalarMultiply_bound n k χ hχ hA hb) a

theorem scalarMultiplier_opNorm_le : ‖scalarMultiplier n k χ hχ A hA hb‖ ≤ A :=
  CompactPairingCompletion.boundedExtension_opNorm_le orbitVolume (pairingData n k)
    (coreScalarMultiply n k χ hχ) A hA (coreScalarMultiply_bound n k χ hχ hA hb)

/-- Real scalar multiplication is symmetric for the genuine metric-volume inner product. -/
theorem inner_scalarMultiplier (a b : Hilbert n k) :
    inner ℝ (scalarMultiplier n k χ hχ A hA hb a) b =
      inner ℝ a (scalarMultiplier n k χ hχ A hA hb b) := by
  let T := scalarMultiplier n k χ hχ A hA hb
  change inner ℝ (T a) b = inner ℝ a (T b)
  refine (inclusion_dense n k).induction_on a
    (isClosed_eq (T.continuous.inner continuous_const) (continuous_id.inner continuous_const)) ?_
  intro v
  refine (inclusion_dense n k).induction_on b
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner T.continuous)) ?_
  intro w
  dsimp only [T]
  exact (congrArg (fun z => inner ℝ z (inclusion n k w))
    (scalarMultiplier_inclusion n k χ hχ A hA hb v)).trans
      ((inner_coreScalarMultiply n k χ hχ v w).trans
        (congrArg (fun z => inner ℝ (inclusion n k v) z)
          (scalarMultiplier_inclusion n k χ hχ A hA hb w).symm))

end TernaryPoly.PolynomialFormConnection
