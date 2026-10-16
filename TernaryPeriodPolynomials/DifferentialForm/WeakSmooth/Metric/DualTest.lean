module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.Restriction
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Gram
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Basic

@[expose] public section

/-! Actual inverse-weighted-Gram coordinate test forms with genuine compact support. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric SymmetricSpaceCharts
  CompactCoordinateIntegration
open scoped ContDiff Distributions Matrix.Norms.Elementwise

/-- The genuine inverse-weighted-Gram basis vector that extracts a fixed form coefficient. -/
def metricDualTestVector (n k : ℕ) (i : Index n k) (x : Coordinates) : FormValue n k :=
  (coordinates n k).symm (fun j => (weightedGram n k x)⁻¹ j i)

/-- Multiply the actual metric-dual vector by an actual compact smooth scalar test. -/
def metricDualTestRaw (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (i : Index n k) (φ : 𝓓(Ω, ℝ)) (x : Coordinates) : FormValue n k :=
  φ x • metricDualTestVector n k i x

theorem metricDualTestRaw_tsupport (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (i : Index n k) (φ : 𝓓(Ω, ℝ)) : tsupport (metricDualTestRaw n k Ω i φ) ⊆ tsupport φ :=
  tsupport_smul_subset_left φ (metricDualTestVector n k i)

theorem metricDualTestRaw_hasCompactSupport (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (i : Index n k) (φ : 𝓓(Ω, ℝ)) : HasCompactSupport (metricDualTestRaw n k Ω i φ) :=
  φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (metricDualTestRaw_tsupport n k Ω i φ)

theorem metricDualTestVector_smooth (n k : ℕ) (i : Index n k) :
    ContDiffOn ℝ ∞ (metricDualTestVector n k i) positiveCoordinates := by
  change ContDiffOn ℝ ∞ ((coordinates n k).symm ∘ (fun x => fun j => (weightedGram n k x)⁻¹ j i)) positiveCoordinates
  apply ContDiff.comp_contDiffOn (𝕜 := ℝ) (E := Coordinates)
    (F := Index n k → ℝ) (G := FormValue n k) (coordinates n k).symm.contDiff
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram_inverse n k) j) i

/-- The true support control upgrades local metric smoothness to global smoothness of the test. -/
theorem metricDualTestRaw_smooth (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (i : Index n k) (φ : 𝓓(Ω, ℝ)) :
    ContDiff ℝ ∞ (metricDualTestRaw n k Ω i φ) := by
  have hφ : ContDiffOn ℝ ∞ (fun x => φ x) positiveCoordinates := φ.contDiff.contDiffOn
  have : IsBoundedSMul ℝ (FormValue n k) :=
    IsBoundedSMul.of_norm_smul_le (α := ℝ) (β := FormValue n k)
      (fun (c : ℝ) (v : FormValue n k) => NormedSpace.norm_smul_le c v)
  have hm : ContDiffOn ℝ ∞ (metricDualTestRaw n k Ω i φ) positiveCoordinates :=
    hφ.smul (metricDualTestVector_smooth n k i)
  exact contDiff_of_tsupport_subset isOpen_positiveCoordinates hm
    ((metricDualTestRaw_tsupport n k Ω i φ).trans (φ.tsupport_subset.trans hΩ))

@[simp] theorem metricDualTestRaw_coordinates (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (i : Index n k) (φ : 𝓓(Ω, ℝ)) (x : Coordinates) :
    coordinates n k (metricDualTestRaw n k Ω i φ x) =
      φ x • (fun j => (weightedGram n k x)⁻¹ j i) := by
  change coordinates n k (φ x • (coordinates n k).symm _) = _
  rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]

end TernaryPoly.PolynomialFormWeakSmooth
