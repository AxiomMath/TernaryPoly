module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.DualTest

@[expose] public section

/-! Exact coefficient extraction by the genuine density-weighted inverse-Gram test. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialFormCoordinates PolynomialFormMetric SymmetricSpaceCharts SymmetricSpaceRiemannian
open scoped Distributions Matrix.Norms.Elementwise

/-- The actual weighted Gram matrix sends its inverse test column to the scalar coordinate test. -/
theorem metricDualTestRaw_gram (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (i : Index n k) (φ : 𝓓(Ω, ℝ)) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    (weightedGram n k x).mulVec (coordinates n k (metricDualTestRaw n k Ω i φ x)) =
      φ x • Pi.single i 1 := by
  rw [metricDualTestRaw_coordinates, Matrix.mulVec_smul]
  have he : (fun j => (weightedGram n k x)⁻¹ j i) =
      (weightedGram n k x)⁻¹.mulVec (Pi.single i 1) := by
    rw [Matrix.mulVec_single_one]
    rfl
  rw [he, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (weightedGram_isUnit n k x hx)),
    Matrix.one_mulVec]

/-- Pairing with the actual inverse-Gram test extracts precisely the chosen actual form
coefficient, including the genuine coordinate density. -/
theorem metricDualTestRaw_pairing (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (i : Index n k) (φ : 𝓓(Ω, ℝ)) (v : FormValue n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    coordinateDensity x * formPairing n k x v (metricDualTestRaw n k Ω i φ x) =
      coordinates n k v i * φ x := by
  rw [← weightedGram_pairing, metricDualTestRaw_gram n k Ω i φ hx,
    dotProduct_smul, dotProduct_single_one]
  simp only [smul_eq_mul, mul_comm]

/-- Exact extraction holds everywhere when the scalar test domain lies inside positive coordinates. -/
theorem metricDualTestRaw_pairing_all (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (i : Index n k) (φ : 𝓓(Ω, ℝ))
    (v : FormValue n k) (x : Coordinates) :
    coordinateDensity x * formPairing n k x v (metricDualTestRaw n k Ω i φ x) =
      coordinates n k v i * φ x := by
  by_cases hx : x ∈ positiveCoordinates
  · exact metricDualTestRaw_pairing n k Ω i φ v hx
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hΩ (φ.tsupport_subset ht)))
    have hr : metricDualTestRaw n k Ω i φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hΩ (φ.tsupport_subset (metricDualTestRaw_tsupport n k Ω i φ ht))))
    rw [hr, formPairing_zero_right, hz, mul_zero, mul_zero]

end TernaryPoly.PolynomialFormWeakSmooth
