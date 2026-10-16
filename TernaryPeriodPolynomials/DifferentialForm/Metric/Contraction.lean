module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Tensor

@[expose] public section

/-! Exact changes of coordinates for the coefficient-valued contraction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix
variable {ι : Type*} [Fintype ι]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

 theorem matrixContraction_swap (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (H : Matrix ι ι ℝ) (v w : ι → V) :
    matrixContraction B H v w = matrixContraction B.flip H.transpose w v := by
  unfold matrixContraction
  exact Finset.sum_comm

theorem matrixContraction_action_left (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (H A : Matrix ι ι ℝ) (v w : ι → V) :
    matrixContraction B H (matrixAction A v) w = matrixContraction B (A.transpose * H) v w := by
  simp only [matrixContraction, matrixAction, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ l, H i j * (A i l * B (v l) (w j))) =
        ∑ i, ∑ l, ∑ j, H i j * (A i l * B (v l) (w j)) := by
      apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, H i j * (A i l * B (v l) (w j)) := Finset.sum_comm
    _ = ∑ l, ∑ j, ∑ i, H i j * (A i l * B (v l) (w j)) := by
      apply Finset.sum_congr rfl; intro l _; exact Finset.sum_comm
    _ = _ := by congr 1; ext l; congr 1; ext j; congr 1; ext i; ring

theorem matrixContraction_action_right (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (H A : Matrix ι ι ℝ) (v w : ι → V) :
    matrixContraction B H v (matrixAction A w) = matrixContraction B (H * A) v w := by
  rw [matrixContraction_swap, matrixContraction_action_left, matrixContraction_swap]
  simp only [LinearMap.flip_flip, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem matrixContraction_action (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (H A : Matrix ι ι ℝ) (v w : ι → V) :
    matrixContraction B H (matrixAction A v) (matrixAction A w) =
      matrixContraction B (A.transpose * H * A) v w := by
  rw [matrixContraction_action_left, matrixContraction_action_right]

theorem matrixContraction_symm (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (H : Matrix ι ι ℝ) (hH : H.transpose = H) (v w : ι → V) :
    matrixContraction B H v w = matrixContraction B H w v := by
  have hb : B.flip = B := by ext v w; exact hB w v
  rw [matrixContraction_swap, hb, hH]

end TernaryPoly.PolynomialFormMetric
