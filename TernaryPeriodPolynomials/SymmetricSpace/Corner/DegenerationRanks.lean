module

public import TernaryPeriodPolynomials.SymmetricSpace.Corner.DegenerationDual

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCornerDegeneration
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceLineBordification

theorem weightedFlag_rank (x y z s t : ℝ) :
    (weightedFlag x y z s t).rank=(Matrix.diagonal ![1,s^2,s^2*t^2]).rank := by
  have hu : (upper x y z).det≠0 := by simp [upper,Matrix.det_fin_three]
  unfold weightedFlag
  rw [Matrix.rank_mul_eq_left_of_det_ne_zero (upper x y z).transpose _
      (by rwa [Matrix.det_transpose])]
  exact Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hu

theorem diagonal_rank_three (a b c : ℝ) :
    (Matrix.diagonal ![a,b,c]).rank=
      (if a=0 then 0 else 1)+(if b=0 then 0 else 1)+(if c=0 then 0 else 1) := by
  classical
  rw [Matrix.rank_diagonal,Fintype.card_subtype,Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter,Fin.sum_univ_succ]
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases hc : c=0 <;> simp [ha,hb,hc]

/-- The primary detector has precisely the rank forced by the first vanishing simple root. -/
theorem A_rank (p : Corner) :
    (A p).rank=if p.2.1.val=0 then 1 else if p.2.2.val=0 then 2 else 3 := by
  rw [A,rank_normalize (ne_of_gt (rawA_trace_pos p)),rawA,weightedFlag_rank,diagonal_rank_three]
  by_cases hs : p.2.1.val=0 <;> by_cases ht : p.2.2.val=0 <;> simp [hs,ht]

/-- Duality exchanges the roles of the two roots in the rank detector. -/
theorem D_rank (p : Corner) :
    (D p).rank=if p.2.2.val=0 then 1 else if p.2.1.val=0 then 2 else 3 := by
  rw [D,rank_conjugate,A_rank]
  rfl

theorem A_rank_one_iff (p : Corner) : (A p).rank=1 ↔ p.2.1.val=0 := by
  rw [A_rank]
  by_cases hs : p.2.1.val=0 <;> by_cases ht : p.2.2.val=0 <;> simp [hs,ht]

theorem A_rank_two_iff (p : Corner) : (A p).rank=2 ↔ 0<p.2.1.val ∧ p.2.2.val=0 := by
  rw [A_rank]
  by_cases h1 : p.2.1.val=0
  · simp [h1]
  · have hp : 0<p.2.1.val := lt_of_le_of_ne p.2.1.property (Ne.symm h1)
    by_cases h2 : p.2.2.val=0 <;> simp [h1,h2,hp]

theorem A_rank_three_iff (p : Corner) : (A p).rank=3 ↔ 0<p.2.1.val ∧ 0<p.2.2.val := by
  rw [A_rank]
  by_cases h1 : p.2.1.val=0
  · simp [h1]
  · have hp : 0<p.2.1.val := lt_of_le_of_ne p.2.1.property (Ne.symm h1)
    by_cases h2 : p.2.2.val=0
    · simp [h1,h2]
    · have hq : 0<p.2.2.val := lt_of_le_of_ne p.2.2.property (Ne.symm h2)
      simp [h1,h2,hp,hq]

theorem D_rank_one_iff (p : Corner) : (D p).rank=1 ↔ p.2.2.val=0 := by
  rw [D,rank_conjugate]
  exact A_rank_one_iff (dualCorner p)

theorem D_rank_two_iff (p : Corner) : (D p).rank=2 ↔ 0<p.2.2.val ∧ p.2.1.val=0 := by
  rw [D,rank_conjugate]
  exact A_rank_two_iff (dualCorner p)

theorem D_rank_three_iff (p : Corner) : (D p).rank=3 ↔ 0<p.2.1.val ∧ 0<p.2.2.val := by
  rw [D,rank_conjugate,A_rank_three_iff]
  exact and_comm

end TernaryPoly.SymmetricSpaceCornerDegeneration
