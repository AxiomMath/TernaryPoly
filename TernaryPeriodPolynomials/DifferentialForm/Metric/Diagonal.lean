module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Tensor

@[expose] public section

/-! Exact diagonal-frame and factorial normalizations for the exterior contraction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem tensorMatrix_diagonal (k : ℕ) (d : ι → ℝ) :
    tensorMatrix k (Matrix.diagonal d) = Matrix.diagonal (fun I : Fin k → ι => ∏ r, d (I r)) := by
  ext I J
  by_cases h : I = J
  · subst J
    simp [tensorMatrix]
  · obtain ⟨r, hr⟩ := Function.ne_iff.mp h
    rw [Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ r) (Matrix.diagonal_apply_ne _ hr)

theorem matrixContraction_diagonal {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (d : ι → ℝ) (v w : ι → V) :
    matrixContraction B (Matrix.diagonal d) v w = ∑ i, d i * B (v i) (w i) := by
  simp [matrixContraction, Matrix.diagonal]

theorem inverse_diagonal_pos (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (Matrix.diagonal (fun i => (d i)⁻¹))⁻¹ = Matrix.diagonal d := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_inv_cancel₀ (ne_of_gt (hd _))]
  exact Matrix.diagonal_one

end TernaryPoly.PolynomialFormMetric
