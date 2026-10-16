module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.AdjointCore
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.CommutatorHilbert
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Hilbert

@[expose] public section


/-! Literal differential and adjoint product rules transported to the actual Hilbert embeddings. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set PolynomialFormHilbert PolynomialCoefficientMetric PolynomialFormCoordinates
  SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped ContDiff Manifold SymmetricSpaceRiemannian

variable (n k : ℕ) (χ : OrbitSpace → ℝ)
  (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (B : ℝ) (hB : 0 ≤ B)
  (hd : ∀ q, scalarSlope χ q ≤ B)

/-- The bounded Hilbert adjoint agrees with the literal compact codifferential cutoff term. -/
theorem exteriorCommutator_adjoint_inclusion (b : Core n (k + 1)) :
    (exteriorCommutator n k χ hχ B hB hd).adjoint (inclusion n (k + 1) b) =
      inclusion n k (coreContractionCommutator n k χ hχ b) := by
  let E := exteriorCommutator n k χ hχ B hB hd
  apply ext_inner_left ℝ
  intro x
  refine (inclusion_dense n k).induction_on x
    (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)) ?_
  intro a
  calc
    _ = inner ℝ (E (inclusion n k a)) (inclusion n (k + 1) b) := E.adjoint_inner_right _ _
    _ = inner ℝ (inclusion n (k + 1) (coreExteriorCommutator n k χ hχ a)) (inclusion n (k + 1) b) :=
      congrArg (fun z => inner ℝ z (inclusion n (k + 1) b))
        (exteriorCommutator_inclusion n k χ hχ B hB hd a)
    _ = _ := inner_coreExterior_coreContraction n k χ hχ a b

include hB hd in
/-- In particular the actual compact adjoint commutator has the same gradient bound. -/
theorem coreContractionCommutator_bound (b : Core n (k + 1)) :
    ‖inclusion n k (coreContractionCommutator n k χ hχ b)‖ ≤
      exteriorCommutatorConstant n k * B * ‖inclusion n (k + 1) b‖ :=
  (congrArg norm (exteriorCommutator_adjoint_inclusion n k χ hχ B hB hd b).symm).trans_le
    (exteriorCommutator_adjoint_bound n k χ hχ B hB hd (inclusion n (k + 1) b))

variable (A : ℝ) (hA : 0 ≤ A) (hv : ∀ q, |χ q| ≤ A)

/-- The true compact differential product rule after the actual L2 inclusion. -/
theorem inclusion_differential_scalarMultiply (a : Core n k) :
    inclusion n (k + 1)
      (compactDifferential (deckRepresentation n) isOpen_univ k (coreScalarMultiply n k χ hχ a)) =
      scalarMultiplier n (k + 1) χ hχ A hA hv
        (inclusion n (k + 1) (compactDifferential (deckRepresentation n) isOpen_univ k a)) +
        exteriorCommutator n k χ hχ B hB hd (inclusion n k a) := by
  let d := compactDifferential (deckRepresentation n) isOpen_univ k
  calc
    _ = inclusion n (k + 1) (coreScalarMultiply n (k + 1) χ hχ (d a)) +
        inclusion n (k + 1) (coreExteriorCommutator n k χ hχ a) :=
      (congrArg (inclusion n (k + 1)) (compactDifferential_coreScalarMultiply n k χ hχ a)).trans (map_add _ _ _)
    _ = _ := congrArg₂ (· + ·) (scalarMultiplier_inclusion n (k + 1) χ hχ A hA hv (d a)).symm
      (exteriorCommutator_inclusion n k χ hχ B hB hd a).symm

/-- The true compact codifferential product rule retains the negative Hilbert-adjoint symbol. -/
theorem inclusion_adjoint_scalarMultiply (b : Core n (k + 1)) :
    inclusion n k (compactAdjoint n k (coreScalarMultiply n (k + 1) χ hχ b)) =
      scalarMultiplier n k χ hχ A hA hv (inclusion n k (compactAdjoint n k b)) -
        (exteriorCommutator n k χ hχ B hB hd).adjoint (inclusion n (k + 1) b) := by
  calc
    _ = inclusion n k (coreScalarMultiply n k χ hχ (compactAdjoint n k b)) -
        inclusion n k (coreContractionCommutator n k χ hχ b) :=
      (congrArg (inclusion n k) (compactAdjoint_coreScalarMultiply n k χ hχ b)).trans (map_sub _ _ _)
    _ = _ := congrArg₂ (· - ·) (scalarMultiplier_inclusion n k χ hχ A hA hv (compactAdjoint n k b)).symm
      (exteriorCommutator_adjoint_inclusion n k χ hχ B hB hd b).symm

end TernaryPoly.PolynomialFormConnection
