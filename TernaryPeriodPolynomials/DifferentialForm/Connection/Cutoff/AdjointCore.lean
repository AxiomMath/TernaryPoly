module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Commutator
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Adjoint
public import TernaryPeriodPolynomials.DifferentialForm.Cutoff

@[expose] public section


/-! The genuine compact codifferential cutoff term is exactly the transpose exterior symbol. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Filter SmoothLocalDeRham SmoothCoveringDeRham SmoothDeRhamGluing
  PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormHilbert PolynomialFormCoordinates
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped ContDiff Manifold SymmetricSpaceRiemannian Topology

/-- The positive metric-contraction cutoff term of the actual compact codifferential. -/
def coreContractionCommutator (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) : Core n (k + 1) →ₗ[ℝ] Core n k :=
  (coreScalarMultiply n k χ hχ).comp (compactAdjoint n k) -
    (compactAdjoint n k).comp (coreScalarMultiply n (k + 1) χ hχ)

theorem coreContractionCommutator_eq (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (b : Core n (k + 1)) :
    coreContractionCommutator n k χ hχ b =
      coreScalarMultiply n k χ hχ (compactAdjoint n k b) -
        compactAdjoint n k (coreScalarMultiply n (k + 1) χ hχ b) := rfl

attribute [irreducible] coreContractionCommutator

/-- The actual codifferential has the negative transpose symbol in its scalar product rule. -/
theorem compactAdjoint_coreScalarMultiply (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (b : Core n (k + 1)) :
    compactAdjoint n k (coreScalarMultiply n (k + 1) χ hχ b) =
      coreScalarMultiply n k χ hχ (compactAdjoint n k b) - coreContractionCommutator n k χ hχ b := by
  apply eq_sub_iff_add_eq.mpr
  exact (add_comm _ _).trans
    (sub_eq_iff_eq_add.mp (coreContractionCommutator_eq n k χ hχ b).symm).symm

/-- The transpose identity uses the genuine global integration-by-parts theorem. -/
theorem inner_coreExterior_coreContraction (n k : ℕ) (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (a : Core n k) (b : Core n (k + 1)) :
    inner ℝ (inclusion n (k + 1) (coreExteriorCommutator n k χ hχ a)) (inclusion n (k + 1) b) =
      inner ℝ (inclusion n k a) (inclusion n k (coreContractionCommutator n k χ hχ b)) := by
  let d := compactDifferential (deckRepresentation n) isOpen_univ k
  have hE : inclusion n (k + 1) (coreExteriorCommutator n k χ hχ a) =
      inclusion n (k + 1) (d (coreScalarMultiply n k χ hχ a)) -
        inclusion n (k + 1) (coreScalarMultiply n (k + 1) χ hχ (d a)) :=
    (congrArg (inclusion n (k + 1)) (coreExteriorCommutator_eq n k χ hχ a)).trans (map_sub _ _ _)
  have hK : inclusion n k (coreContractionCommutator n k χ hχ b) =
      inclusion n k (coreScalarMultiply n k χ hχ (compactAdjoint n k b)) -
        inclusion n k (compactAdjoint n k (coreScalarMultiply n (k + 1) χ hχ b)) :=
    (congrArg (inclusion n k) (coreContractionCommutator_eq n k χ hχ b)).trans (map_sub _ _ _)
  have hfirst : inner ℝ (inclusion n (k + 1) (d (coreScalarMultiply n k χ hχ a))) (inclusion n (k + 1) b) =
      inner ℝ (inclusion n k a) (inclusion n k (coreScalarMultiply n k χ hχ (compactAdjoint n k b))) :=
    (inner_compactDifferential_compactAdjoint n k (coreScalarMultiply n k χ hχ a) b).trans
      (inner_coreScalarMultiply n k χ hχ a (compactAdjoint n k b))
  have hsecond : inner ℝ (inclusion n (k + 1) (coreScalarMultiply n (k + 1) χ hχ (d a)))
      (inclusion n (k + 1) b) =
      inner ℝ (inclusion n k a) (inclusion n k (compactAdjoint n k (coreScalarMultiply n (k + 1) χ hχ b))) :=
    (inner_coreScalarMultiply n (k + 1) χ hχ (d a) b).trans
      (inner_compactDifferential_compactAdjoint n k a (coreScalarMultiply n (k + 1) χ hχ b))
  calc
    _ = inner ℝ (inclusion n (k + 1) (d (coreScalarMultiply n k χ hχ a))) (inclusion n (k + 1) b) -
        inner ℝ (inclusion n (k + 1) (coreScalarMultiply n (k + 1) χ hχ (d a))) (inclusion n (k + 1) b) :=
      (congrArg (fun z => inner ℝ z (inclusion n (k + 1) b)) hE).trans (inner_sub_left _ _ _)
    _ = inner ℝ (inclusion n k a) (inclusion n k (coreScalarMultiply n k χ hχ (compactAdjoint n k b))) -
        inner ℝ (inclusion n k a) (inclusion n k (compactAdjoint n k (coreScalarMultiply n (k + 1) χ hχ b))) :=
      congrArg₂ (· - ·) hfirst hsecond
    _ = _ := (inner_sub_right _ _ _).symm.trans
      (congrArg (fun z => inner ℝ (inclusion n k a) z) hK.symm)

end TernaryPoly.PolynomialFormConnection
