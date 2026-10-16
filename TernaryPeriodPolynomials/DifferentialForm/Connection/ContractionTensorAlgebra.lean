module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.InverseGram
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.ContractionAlgebra

@[expose] public section

/-! Exact finite-dimensional cancellation for the genuine inverse-metric contraction. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open scoped Matrix.Norms.Elementwise

theorem tangentConnection_matrixAction (x u : Coordinates) :
    (fun i : Fin 5 => tangentConnection x u (Pi.single i 1)) =
      matrixAction (tangentConnectionMatrix x u).transpose (fun i => Pi.single i 1) := by
  funext i
  ext j
  simp only [matrixAction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Matrix.transpose_apply, tangentConnectionMatrix, LinearMap.toMatrix'_apply]
  rfl

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem bilinearContraction_add_matrix (B : Coordinates →ₗ[ℝ] Coordinates →ₗ[ℝ] W)
    (H J : Matrix (Fin 5) (Fin 5) ℝ) (v w : Fin 5 → Coordinates) :
    bilinearContraction B (H + J) v w = bilinearContraction B H v w + bilinearContraction B J v w := by
  simp only [bilinearContraction, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem bilinearContraction_neg_matrix (B : Coordinates →ₗ[ℝ] Coordinates →ₗ[ℝ] W)
    (H : Matrix (Fin 5) (Fin 5) ℝ) (v w : Fin 5 → Coordinates) :
    bilinearContraction B (-H) v w = -bilinearContraction B H v w := by
  simp only [bilinearContraction, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]

/-- The two tangent corrections cancel the actual inverse-Gram derivative. -/
theorem bilinearContraction_connection_cancel (B : Coordinates →ₗ[ℝ] Coordinates →ₗ[ℝ] W)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (u : Coordinates) :
    bilinearContraction B (fderiv ℝ inverseGram x u) (fun i => Pi.single i 1) (fun i => Pi.single i 1) +
      bilinearContraction B (inverseGram x) (fun i => tangentConnection x u (Pi.single i 1)) (fun i => Pi.single i 1) +
      bilinearContraction B (inverseGram x) (fun i => Pi.single i 1) (fun i => tangentConnection x u (Pi.single i 1)) = 0 := by
  rw [inverseGramDerivative x hx u, tangentConnection_matrixAction,
    bilinearContraction_action_left, bilinearContraction_action_right,
    Matrix.transpose_transpose, bilinearContraction_neg_matrix, bilinearContraction_add_matrix]
  abel

end TernaryPoly.PolynomialFormConnection
