module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.AdjointHilbert
public import TernaryPeriodPolynomials.DifferentialForm.WeakTests
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.WeakAlgebra

@[expose] public section


/-! Actual compact-test transposition transports both maximal graphs through scalar cutoffs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set PolynomialFormHilbert PolynomialCoefficientMetric PolynomialFormCoordinates
  SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped ContDiff Manifold SymmetricSpaceRiemannian LinearPMap

attribute [local irreducible] scalarMultiplier exteriorCommutator PolynomialFormHilbert.inclusion
  maximalDifferential maximalCodifferential

variable (n k : ℕ) (χ : OrbitSpace → ℝ)
  (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (B : ℝ) (hB : 0 ≤ B)
  (hd : ∀ q, scalarSlope χ q ≤ B) (A : ℝ) (hA : 0 ≤ A) (hv : ∀ q, |χ q| ≤ A)

/-- The maximal exterior derivative obeys the genuine scalar Leibniz rule on its full weak domain. -/
theorem maximalDifferential_scalarMultiply (x : Hilbert n k) (z : Hilbert n (k + 1))
    (hx : (x, z) ∈ (maximalDifferential n k).graph) :
    (scalarMultiplier n k χ hχ A hA hv x,
      scalarMultiplier n (k + 1) χ hχ A hA hv z + exteriorCommutator n k χ hχ B hB hd x) ∈
        (maximalDifferential n k).graph := by
  let M0 := scalarMultiplier n k χ hχ A hA hv
  let M1 := scalarMultiplier n (k + 1) χ hχ A hA hv
  let E := exteriorCommutator n k χ hχ B hB hd
  have hw := (mem_maximalDifferential_graph_iff n k x z).mp hx
  apply (mem_maximalDifferential_graph_iff n k (M0 x) (M1 z + E x)).mpr
  intro b
  exact weakScalar_add_inner M0 M1 E x z (inclusion n (k + 1) b)
    (inclusion n (k + 1) (coreScalarMultiply n (k + 1) χ hχ b))
    (inclusion n k (compactAdjoint n k b))
    (inclusion n k (compactAdjoint n k (coreScalarMultiply n (k + 1) χ hχ b)))
    (inner_scalarMultiplier n k χ hχ A hA hv x (inclusion n k (compactAdjoint n k b)))
    (inner_scalarMultiplier n (k + 1) χ hχ A hA hv z (inclusion n (k + 1) b))
    (scalarMultiplier_inclusion n (k + 1) χ hχ A hA hv b)
    (inclusion_adjoint_scalarMultiply n k χ hχ B hB hd A hA hv b)
    (hw (coreScalarMultiply n (k + 1) χ hχ b))

/-- The maximal codifferential obeys the opposite transpose-symbol product rule on its full weak domain. -/
theorem maximalCodifferential_scalarMultiply (x : Hilbert n (k + 1)) (z : Hilbert n k)
    (hx : (x, z) ∈ (maximalCodifferential n k).graph) :
    (scalarMultiplier n (k + 1) χ hχ A hA hv x,
      scalarMultiplier n k χ hχ A hA hv z - (exteriorCommutator n k χ hχ B hB hd).adjoint x) ∈
        (maximalCodifferential n k).graph := by
  let M0 := scalarMultiplier n k χ hχ A hA hv
  let M1 := scalarMultiplier n (k + 1) χ hχ A hA hv
  let E := exteriorCommutator n k χ hχ B hB hd
  let d := compactDifferential (deckRepresentation n) isOpen_univ k
  have hw := (mem_maximalCodifferential_graph_iff n k x z).mp hx
  apply (mem_maximalCodifferential_graph_iff n k (M1 x) (M0 z - E.adjoint x)).mpr
  intro a
  exact weakScalar_sub_inner M0 M1 E x z (inclusion n k a)
    (inclusion n k (coreScalarMultiply n k χ hχ a))
    (inclusion n (k + 1) (d a))
    (inclusion n (k + 1) (d (coreScalarMultiply n k χ hχ a)))
    (inner_scalarMultiplier n k χ hχ A hA hv z (inclusion n k a))
    (inner_scalarMultiplier n (k + 1) χ hχ A hA hv x (inclusion n (k + 1) (d a)))
    (scalarMultiplier_inclusion n k χ hχ A hA hv a)
    (inclusion_differential_scalarMultiply n k χ hχ B hB hd A hA hv a)
    (hw (coreScalarMultiply n k χ hχ a))

end TernaryPoly.PolynomialFormConnection
