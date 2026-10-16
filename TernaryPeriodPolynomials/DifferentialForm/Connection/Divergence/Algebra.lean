module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence.Density

@[expose] public section


/-! Exact finite matrix cancellations in the divergence of a metric-dual covector. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix

theorem divergence_metric_dual_algebra (H : Matrix (Fin 5) (Fin 5) ℝ)
    (K : Fin 5 → Matrix (Fin 5) (Fin 5) ℝ) (a : Fin 5 → ℝ) (b : Fin 5 → Fin 5 → ℝ)
    (hK : ∀ i r j, K i r j = K j r i) :
    (∑ i, ((K i).trace * (∑ j, H i j * a j) +
      ∑ j, ((-(K i * H + H * (K i).transpose)) i j * a j +
        H i j * (b i j + ∑ r, K i r j * a r)))) =
      ∑ i, ∑ j, H i j * b i j := by
  have h1 : (∑ i, ∑ j, ∑ r, K i r r * (H i j * a j)) =
      ∑ i, ∑ j, ∑ r, (K i i r * H r j) * a j := by
    calc
      _ = ∑ i, ∑ r, ∑ j, K i r r * (H i j * a j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ r, ∑ i, ∑ j, K i r r * (H i j * a j) := Finset.sum_comm
      _ = ∑ r, ∑ j, ∑ i, (K r r i * H i j) * a j := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [hK i r r]
        ring
  have h2 : (∑ i, ∑ j, ∑ r, (H i r * K i j r) * a j) =
      ∑ i, ∑ j, ∑ r, H i j * (K i r j * a r) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [Matrix.trace, Matrix.diag, Matrix.neg_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, neg_add_rev, add_mul, neg_mul, mul_add,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [← h1, h2]
  ring

end TernaryPoly.PolynomialFormConnection
