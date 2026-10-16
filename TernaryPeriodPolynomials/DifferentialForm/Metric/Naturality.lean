module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Pointwise

@[expose] public section


/-! Frame independence of the inverse-Gram contraction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix SymmetricSpaceCharts PolynomialCoefficientMetric

/-- Inverse Gram matrices obey the contravariant metric transformation law. -/
theorem inverse_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H L : Matrix ι ι ℝ) (hG : G.PosDef) (h : L.transpose * H * L = G) :
    L * G⁻¹ * L.transpose = H⁻¹ := by
  have hd : L.det ≠ 0 := by
    intro hz
    have hg : G.det ≠ 0 := ne_of_gt hG.det_pos
    apply hg
    rw [← h, Matrix.det_mul, hz, mul_zero]
  obtain ⟨l, rfl⟩ := (L.isUnit_iff_isUnit_det).mpr (isUnit_iff_ne_zero.mpr hd)
  rw [← h, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp [mul_assoc, ← Matrix.transpose_nonsing_inv]
  rw [← Matrix.transpose_mul]
  simp

/-- Pullback of a genuine alternating map corresponds to the same tensor transformation. -/
theorem contraction_pullback {n k : ℕ} (B : Coefficients n →ₗ[ℝ] Coefficients n →ₗ[ℝ] ℝ)
    (H : Matrix (Fin 5) (Fin 5) ℝ) (L : Coordinates →L[ℝ] Coordinates) (a b : FormValue n k) :
    matrixContraction B (tensorMatrix k H)
      (formCoordinates (a.compContinuousLinearMap L))
      (formCoordinates (b.compContinuousLinearMap L)) =
      matrixContraction B
        (tensorMatrix k (LinearMap.toMatrix' L.toLinearMap * H *
          (LinearMap.toMatrix' L.toLinearMap).transpose)) (formCoordinates a) (formCoordinates b) := by
  rw [formCoordinates_comp, formCoordinates_comp, matrixContraction_action]
  simp only [tensorMatrix_transpose, Matrix.transpose_transpose, tensorMatrix_mul]

/-- Exact frame independence, for every finite alternating degree. -/
theorem contraction_isometry {n k : ℕ} (B : Coefficients n →ₗ[ℝ] Coefficients n →ₗ[ℝ] ℝ)
    (G H : Matrix (Fin 5) (Fin 5) ℝ) (hG : G.PosDef)
    (L : Coordinates →L[ℝ] Coordinates)
    (hL : (LinearMap.toMatrix' L.toLinearMap).transpose * H *
      LinearMap.toMatrix' L.toLinearMap = G) (a b : FormValue n k) :
    matrixContraction B (tensorMatrix k G⁻¹)
      (formCoordinates (a.compContinuousLinearMap L))
      (formCoordinates (b.compContinuousLinearMap L)) =
      matrixContraction B (tensorMatrix k H⁻¹) (formCoordinates a) (formCoordinates b) := by
  rw [contraction_pullback, inverse_congruence G H _ hG hL]

end TernaryPoly.PolynomialFormMetric
