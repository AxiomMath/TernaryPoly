module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.GLTangent

@[expose] public section


/-! Naturality of the actual polynomial infinitesimal action under inverse substitution. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem hasDerivAt_identity_affine (A : Mat) :
    HasDerivAt (fun t : ℝ => (1 : Mat) - t • A) (-A) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  convert! (hasDerivAt_const (0 : ℝ) ((1 : Mat) i j)).sub
    ((hasDerivAt_id (0 : ℝ)).mul_const (A i j)) using 1
  simp

theorem hasDerivAt_conjugate_identity_affine (G A : Mat) :
    HasDerivAt (fun t : ℝ => G * ((1 : Mat) - t • A) * G⁻¹) (-(G * A * G⁻¹)) 0 := by
  have h := hasDerivAt_matrix_product
    (hasDerivAt_matrix_product (hasDerivAt_const (0 : ℝ) G) (hasDerivAt_identity_affine A))
    (hasDerivAt_const (0 : ℝ) G⁻¹)
  convert! h using 1
  simp

theorem coefficientSubstitution_conjugation (n : ℕ) (G E : Mat) (hG : IsUnit G) (p : Coefficients n) :
    coefficientSubstitution n (G * E * G⁻¹) (coefficientSubstitution n G⁻¹ p) =
      coefficientSubstitution n G⁻¹ (coefficientSubstitution n E p) := by
  rw [coefficientSubstitution_mul, coefficientSubstitution_mul]
  simp only [← mul_assoc, Matrix.nonsing_inv_mul G (G.isUnit_iff_isUnit_det.mp hG), one_mul]

/-- Intertwining is derived by differentiating the literal reversed substitution composition. -/
theorem coefficientInfinitesimal_conjugation (n : ℕ) (G A : Mat) (hG : IsUnit G) (p : Coefficients n) :
    coefficientInfinitesimal n (G * A * G⁻¹) (coefficientSubstitution n G⁻¹ p) =
      coefficientSubstitution n G⁻¹ (coefficientInfinitesimal n A p) := by
  have hdet := G.isUnit_iff_isUnit_det.mp hG
  have h0 : G * ((1 : Mat) - (0 : ℝ) • A) * G⁻¹ = 1 := by
    simp only [zero_smul, sub_zero, mul_one, Matrix.mul_nonsing_inv G hdet]
  have h1 := hasDerivAt_coefficientSubstitution_identity n (G * A * G⁻¹)
    (fun t : ℝ => G * ((1 : Mat) - t • A) * G⁻¹)
    (hasDerivAt_conjugate_identity_affine G A) h0 (coefficientSubstitution n G⁻¹ p)
  have h2 := hasDerivAt_fixedSubstitution n G⁻¹ _ _
    (hasDerivAt_coefficientSubstitution_identity n A (fun t : ℝ => (1 : Mat) - t • A)
      (hasDerivAt_identity_affine A) (by simp) p)
  have he : (fun t : ℝ => coefficientSubstitution n (G * ((1 : Mat) - t • A) * G⁻¹)
      (coefficientSubstitution n G⁻¹ p)) =
      (fun t : ℝ => coefficientSubstitution n G⁻¹ (coefficientSubstitution n ((1 : Mat) - t • A) p)) := by
    funext t
    exact coefficientSubstitution_conjugation n G _ hG p
  rw [he] at h1
  exact h1.unique h2

end TernaryPoly.PolynomialFormConnection
