module

public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.FormalAdjoint

@[expose] public section


/-! Exact reindexing of first-order coefficient sums. -/
namespace TernaryPoly.CompactCoordinateIntegration
open Finset

theorem sum_four_last_first {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
      apply sum_congr rfl; intro a _
      apply sum_congr rfl; intro b _
      exact sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply sum_congr rfl; intro a _
      exact sum_comm
    _ = _ := sum_comm

theorem matrixFirstOrder_three_indices {E I J A B C : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    (v : C → E) (a b : J → I → A → B → C → E → ℝ) (f : I → E → ℝ) (j : J) (x : E) :
    matrixFirstOrder (fun q : A × B × C => v q.2.2)
      (fun j i q => a j i q.1 q.2.1 q.2.2) (fun j i q => b j i q.1 q.2.1 q.2.2) f j x =
      ∑ l, ∑ t, ∑ d, ∑ i, firstOrder (v d) (a j i l t d) (b j i l t d) (f i) x := by
  simp only [matrixFirstOrder, Fintype.sum_prod_type]
  exact (sum_four_last_first (fun l t d i => firstOrder (v d) (a j i l t d) (b j i l t d) (f i) x)).symm

end TernaryPoly.CompactCoordinateIntegration
