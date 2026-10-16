module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SupportNormals
public import TernaryPeriodPolynomials.Building.Reference.CoefficientMatrices
public import Lean.Elab.Tactic.Omega

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.OrdinaryResidueSupport
open ModThreeGoodAction GoodIntegralNormalization
open ReferenceCoefficientMatrices

/-- Literal right row multiplication by the order-three matrix. -/
lemma row_a (v : IntegralVector) : Matrix.vecMul v a.val=![v 1,-(v 0+v 1),v 2] := by
  funext i
  fin_cases i <;> simp [a,aMatrix,Matrix.vecMul,dotProduct,Fin.sum_univ_three,add_comm]

/-- The second literal transform is also the inverse, so both inverse conventions occur. -/
lemma row_a_sq (v : IntegralVector) : Matrix.vecMul v (a^2).val= ![-(v 0+v 1),v 0,v 2] := by
  rw [← a_inv_eq_sq]
  change Matrix.vecMul v aInverseMatrix= ![-(v 0+v 1),v 0,v 2]
  funext i
  fin_cases i <;> simp [aInverseMatrix,Matrix.vecMul,dotProduct,Fin.sum_univ_three,add_comm]

/-- Two nonzero coordinates exclude every coordinate normal line. -/
lemma not_coordinate_of_first_pair (v : IntegralVector) (hv : Primitive v)
    (h0 : v 0≠0) (h1 : v 1≠0) : ¬Coordinate (normalOfRow v hv) := by
  intro hc
  obtain ⟨i,hi⟩ := (coordinate_normalOfRow_iff v hv).mp hc
  fin_cases i
  · exact h1 (hi 1 (by decide))
  · exact h0 (hi 0 (by decide))
  · exact h0 (hi 0 (by decide))

lemma row_a_noncoordinate (v : IntegralVector) (hv : Primitive v)
    (h0 : 0<v 0) (h1 : 0<v 1) : ¬Coordinate (rowAction a (normalOfRow v hv)) := by
  rw [rowAction_normalOfRow]
  apply not_coordinate_of_first_pair
  · rw [row_a]; exact h1.ne'
  · rw [row_a]
    change -(v 0+v 1)≠0
    exact neg_ne_zero.mpr (add_pos h0 h1).ne'

lemma row_a_sq_noncoordinate (v : IntegralVector) (hv : Primitive v)
    (h0 : 0<v 0) (h1 : 0<v 1) : ¬Coordinate (rowAction (a^2) (normalOfRow v hv)) := by
  rw [rowAction_normalOfRow]
  apply not_coordinate_of_first_pair
  · rw [row_a_sq]
    change -(v 0+v 1)≠0
    exact neg_ne_zero.mpr (add_pos h0 h1).ne'
  · rw [row_a_sq]; exact h0.ne'

/-- Primitive height grows by the positive second coordinate under the first transform. -/
lemma height_row_a (v : IntegralVector) (hv : Primitive v)
    (h0 : 0<v 0) (h1 : 0<v 1) (h2 : 0≤v 2) :
    (height (rowAction a (normalOfRow v hv)) : ℤ)=height (normalOfRow v hv)+v 1 := by
  rw [rowAction_normalOfRow,height_normalOfRow,height_normalOfRow,row_a]
  simp only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Nat.cast_add,Int.natCast_natAbs,abs_neg,
    abs_of_pos h0,abs_of_pos h1,abs_of_pos (add_pos h0 h1),abs_of_nonneg h2]
  omega

/-- Primitive height grows by the positive first coordinate under the inverse transform. -/
lemma height_row_a_sq (v : IntegralVector) (hv : Primitive v)
    (h0 : 0<v 0) (h1 : 0<v 1) (h2 : 0≤v 2) :
    (height (rowAction (a^2) (normalOfRow v hv)) : ℤ)=height (normalOfRow v hv)+v 0 := by
  rw [rowAction_normalOfRow,height_normalOfRow,height_normalOfRow,row_a_sq]
  simp only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Nat.cast_add,Int.natCast_natAbs,abs_neg,
    abs_of_pos h0,abs_of_pos h1,abs_of_pos (add_pos h0 h1),abs_of_nonneg h2]
  omega

lemma height_lt_row_a (v : IntegralVector) (hv : Primitive v)
    (h0 : 0<v 0) (h1 : 0<v 1) (h2 : 0≤v 2) :
    height (normalOfRow v hv)<height (rowAction a (normalOfRow v hv)) := by
  have he := height_row_a v hv h0 h1 h2
  omega

lemma height_lt_row_a_sq (v : IntegralVector) (hv : Primitive v)
    (h0 : 0<v 0) (h1 : 0<v 1) (h2 : 0≤v 2) :
    height (normalOfRow v hv)<height (rowAction (a^2) (normalOfRow v hv)) := by
  have he := height_row_a_sq v hv h0 h1 h2
  omega

end TernaryPoly.OrdinaryResidueSupport
