module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Commutator
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.BoundedTarget
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section


/-! Genuine bounded exterior commutators on the actual metric-volume Hilbert completions. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Filter MeasureTheory PolynomialFormHilbert SymmetricSpaceCharts SymmetricSpaceCovering
  SymmetricSpaceRiemannian Manifold
open scoped ContDiff Manifold SymmetricSpaceRiemannian Topology

/-- The fixed constant depends only on coefficient degree and exterior degree. -/
def exteriorCommutatorConstant (n k : ℕ) : ℝ :=
  Real.sqrt (exists_coreExteriorCommutator_square_bound n k).choose

theorem exteriorCommutatorConstant_nonneg (n k : ℕ) : 0 ≤ exteriorCommutatorConstant n k :=
  Real.sqrt_nonneg _

theorem coreExteriorCommutator_bound (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q, scalarSlope χ q ≤ B) (a : Core n k) :
    ‖inclusion n (k + 1) (coreExteriorCommutator n k χ hχ a)‖ ≤
      exteriorCommutatorConstant n k * B * ‖inclusion n k a‖ := by
  let C := (exists_coreExteriorCommutator_square_bound n k).choose
  have hC : 0 ≤ C := (exists_coreExteriorCommutator_square_bound n k).choose_spec.1
  have hh := (exists_coreExteriorCommutator_square_bound n k).choose_spec.2 χ hχ B hB hb a
  have he : exteriorCommutatorConstant n k ^ 2 = C := Real.sq_sqrt hC
  have hp : 0 ≤ exteriorCommutatorConstant n k * B * ‖inclusion n k a‖ :=
    mul_nonneg (mul_nonneg (exteriorCommutatorConstant_nonneg n k) hB) (norm_nonneg _)
  have hm : (exteriorCommutatorConstant n k * B * ‖inclusion n k a‖) ^ 2 =
      C * B ^ 2 * ‖inclusion n k a‖ ^ 2 :=
    (mul_pow (exteriorCommutatorConstant n k * B) ‖inclusion n k a‖ 2).trans
      ((congrArg (· * ‖inclusion n k a‖ ^ 2) (mul_pow (exteriorCommutatorConstant n k) B 2)).trans
        (congrArg (fun t => t * B ^ 2 * ‖inclusion n k a‖ ^ 2) he))
  exact (sq_le_sq₀ (norm_nonneg _) hp).mp (hh.trans_eq hm.symm)

/-- Extension of the literal compact exterior commutator, not an assumed bounded operator. -/
def exteriorCommutator (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q, scalarSlope χ q ≤ B) : Hilbert n k →L[ℝ] Hilbert n (k + 1) :=
  CompactPairingCompletion.boundedTargetExtension orbitVolume (pairingData n k)
    ((inclusion n (k + 1)).comp (coreExteriorCommutator n k χ hχ))
    (exteriorCommutatorConstant n k * B) (coreExteriorCommutator_bound n k χ hχ B hB hb)

theorem exteriorCommutator_inclusion (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q, scalarSlope χ q ≤ B) (a : Core n k) :
    exteriorCommutator n k χ hχ B hB hb (inclusion n k a) =
      inclusion n (k + 1) (coreExteriorCommutator n k χ hχ a) :=
  CompactPairingCompletion.boundedTargetExtension_inclusion orbitVolume (pairingData n k)
    ((inclusion n (k + 1)).comp (coreExteriorCommutator n k χ hχ))
    (exteriorCommutatorConstant n k * B) (coreExteriorCommutator_bound n k χ hχ B hB hb) a

theorem exteriorCommutator_bound (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q, scalarSlope χ q ≤ B) (a : Hilbert n k) :
    ‖exteriorCommutator n k χ hχ B hB hb a‖ ≤ exteriorCommutatorConstant n k * B * ‖a‖ := by
  let E := exteriorCommutator n k χ hχ B hB hb
  refine (inclusion_dense n k).induction_on a
    (isClosed_le E.continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro w
  exact (congrArg norm (exteriorCommutator_inclusion n k χ hχ B hB hb w)).trans_le
    (coreExteriorCommutator_bound n k χ hχ B hB hb w)

theorem exteriorCommutator_opNorm_le (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q, scalarSlope χ q ≤ B) :
    ‖exteriorCommutator n k χ hχ B hB hb‖ ≤ exteriorCommutatorConstant n k * B :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (exteriorCommutatorConstant_nonneg n k) hB)
    (exteriorCommutator_bound n k χ hχ B hB hb)

theorem exteriorCommutator_adjoint_bound (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q, scalarSlope χ q ≤ B) (a : Hilbert n (k + 1)) :
    ‖(exteriorCommutator n k χ hχ B hB hb).adjoint a‖ ≤
      exteriorCommutatorConstant n k * B * ‖a‖ := by
  have hn : ‖(exteriorCommutator n k χ hχ B hB hb).adjoint‖ ≤ exteriorCommutatorConstant n k * B := by
    exact (ContinuousLinearMap.adjoint.norm_map (exteriorCommutator n k χ hχ B hB hb)).trans_le
      (exteriorCommutator_opNorm_le n k χ hχ B hB hb)
  exact ((exteriorCommutator n k χ hχ B hB hb).adjoint.le_opNorm a).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg a))

end TernaryPoly.PolynomialFormConnection
