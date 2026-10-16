module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Algebra

@[expose] public section


/-! Derivatives of the literal coefficient metric at arbitrary positive forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- Fixed substitution preserves genuine vector derivatives. -/
theorem hasDerivAt_fixedSubstitution (n : ℕ) (Q : Mat) (f : ℝ → Coefficients n)
    (p : Coefficients n) (hf : HasDerivAt f p 0) :
    HasDerivAt (fun t => coefficientSubstitution n Q (f t)) (coefficientSubstitution n Q p) 0 :=
  ((coefficientSubstitution n Q).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0 hf

/-- Translate an arbitrary invertible matrix curve to the identity. -/
theorem hasDerivAt_translatedSubstitution (n : ℕ) (A : ℝ → Mat) (Q R : Mat)
    (hQ : IsUnit Q) (hA : HasDerivAt A R 0) (h0 : A 0 = Q) (p : Coefficients n) :
    HasDerivAt (fun t => coefficientSubstitution n (A t * Q⁻¹) p)
      (-coefficientInfinitesimal n (R * Q⁻¹) p) 0 := by
  have hdet : IsUnit Q.det := Q.isUnit_iff_isUnit_det.mp hQ
  have hE : HasDerivAt (fun t => A t * Q⁻¹) (R * Q⁻¹) 0 := by
    simpa using hasDerivAt_matrix_product hA (hasDerivAt_const (0 : ℝ) Q⁻¹)
  have hE0 : A 0 * Q⁻¹ = 1 := by rw [h0]; exact Matrix.mul_nonsing_inv Q hdet
  have hd := hasDerivAt_coefficientSubstitution_identity n (-(R * Q⁻¹))
    (fun t => A t * Q⁻¹) (by simpa using hE) hE0 p
  simpa only [coefficientInfinitesimal_neg] using hd

/-- Differentiate the genuine substitution at every invertible base matrix. -/
theorem hasDerivAt_coefficientSubstitution (n : ℕ) (A : ℝ → Mat) (Q R : Mat)
    (hQ : IsUnit Q) (hA : HasDerivAt A R 0) (h0 : A 0 = Q) (p : Coefficients n) :
    HasDerivAt (fun t => coefficientSubstitution n (A t) p)
      (-coefficientSubstitution n Q (coefficientInfinitesimal n (R * Q⁻¹) p)) 0 := by
  have hc := hasDerivAt_fixedSubstitution n Q _ _
    (hasDerivAt_translatedSubstitution n A Q R hQ hA h0 p)
  rw [map_neg] at hc
  have he (t : ℝ) : coefficientSubstitution n Q (coefficientSubstitution n (A t * Q⁻¹) p) =
      coefficientSubstitution n (A t) p := by
    rw [coefficientSubstitution_mul, mul_assoc,
      Matrix.nonsing_inv_mul Q (Q.isUnit_iff_isUnit_det.mp hQ), mul_one]
  have hf : (fun t => coefficientSubstitution n Q (coefficientSubstitution n (A t * Q⁻¹) p)) =
      (fun t => coefficientSubstitution n (A t) p) := funext he
  rw [hf] at hc
  exact hc

/-- Scalar metric differentiation uses the same polynomial infinitesimal endomorphism. -/
theorem hasDerivAt_matrixMetric (n : ℕ) (A : ℝ → Mat) (Q R : Mat)
    (hQ : IsUnit Q) (hA : HasDerivAt A R 0) (h0 : A 0 = Q) (p q : Coefficients n) :
    HasDerivAt (fun t => matrixContinuousBilin n (A t) p q)
      (-(matrixContinuousBilin n Q p (coefficientInfinitesimal n (R * Q⁻¹) q))) 0 := by
  have hd := (hasDerivAt_const (0 : ℝ) p).inner ℝ
    (hasDerivAt_coefficientSubstitution n A Q R hQ hA h0 q)
  simpa [coefficient_inner, matrixContinuousBilin_apply, matrixPairing] using hd

end TernaryPoly.PolynomialFormConnection
