module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Derivative

@[expose] public section


/-! Symmetry of the actual logarithmic metric derivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- The infinitesimal logarithmic derivative is self-adjoint for the genuine Q metric. -/
theorem metricInfinitesimal_selfAdjoint (n : ℕ) (Q R : Mat) (hQ : IsUnit Q)
    (hQs : Q.transpose = Q) (hRs : R.transpose = R) (p q : Coefficients n) :
    matrixContinuousBilin n Q (coefficientInfinitesimal n (R * Q⁻¹) p) q =
      matrixContinuousBilin n Q p (coefficientInfinitesimal n (R * Q⁻¹) q) := by
  have hA : HasDerivAt (fun t : ℝ => Q + t • R) R 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    convert! (hasDerivAt_const (0 : ℝ) (Q i j)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (R i j)) using 1
    simp
  have h0 : Q + (0 : ℝ) • R = Q := by simp
  have h1 := hasDerivAt_matrixMetric n (fun t => Q + t • R) Q R hQ hA h0 p q
  have h2 := hasDerivAt_matrixMetric n (fun t => Q + t • R) Q R hQ hA h0 q p
  have he : (fun t : ℝ => matrixContinuousBilin n (Q + t • R) p q) =
      (fun t : ℝ => matrixContinuousBilin n (Q + t • R) q p) := by
    funext t
    exact matrixPairing_symmetric _ (by simp [hQs, hRs]) p.val q.val
  rw [he] at h1
  have hn := neg_injective (h1.unique h2)
  calc
    _ = matrixContinuousBilin n Q q (coefficientInfinitesimal n (R * Q⁻¹) p) :=
      matrixPairing_symmetric Q hQs _ _
    _ = _ := hn.symm

end TernaryPoly.PolynomialFormConnection
