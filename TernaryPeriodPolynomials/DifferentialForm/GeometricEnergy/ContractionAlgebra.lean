module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Exterior

@[expose] public section

/-! Vector-valued inverse-Gram contractions and their genuine frame change. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialFormMetric
variable {ι : Type*} [Fintype ι]
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def bilinearContraction (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (H : Matrix ι ι ℝ) (v w : ι → V) : W :=
  ∑ i, ∑ j, H i j • B (v i) (w j)

theorem bilinearContraction_swap (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (H : Matrix ι ι ℝ) (v w : ι → V) :
    bilinearContraction B H v w = bilinearContraction B.flip H.transpose w v := by
  unfold bilinearContraction
  exact Finset.sum_comm

theorem bilinearContraction_action_left (B : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (H A : Matrix ι ι ℝ) (v w : ι → V) :
    bilinearContraction B H (matrixAction A v) w = bilinearContraction B (A.transpose * H) v w := by
  simp only [bilinearContraction, matrixAction, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_smul, Finset.smul_sum]
  calc
    (∑ i, ∑ j, ∑ l, H i j • (A i l • B (v l) (w j))) =
        ∑ i, ∑ l, ∑ j, H i j • (A i l • B (v l) (w j)) := by
      apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, H i j • (A i l • B (v l) (w j)) := Finset.sum_comm
    _ = ∑ l, ∑ j, ∑ i, H i j • (A i l • B (v l) (w j)) := by
      apply Finset.sum_congr rfl; intro l _; exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro i _
      rw [smul_smul, mul_comm]

theorem bilinearContraction_action_right (B : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (H A : Matrix ι ι ℝ) (v w : ι → V) :
    bilinearContraction B H v (matrixAction A w) = bilinearContraction B (H * A) v w := by
  rw [bilinearContraction_swap, bilinearContraction_action_left, bilinearContraction_swap]
  simp only [LinearMap.flip_flip, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem bilinearContraction_action (B : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (H A : Matrix ι ι ℝ) (v w : ι → V) :
    bilinearContraction B H (matrixAction A v) (matrixAction A w) =
      bilinearContraction B (A.transpose * H * A) v w := by
  rw [bilinearContraction_action_left, bilinearContraction_action_right]

end TernaryPoly.PolynomialFormGeometricEnergy
