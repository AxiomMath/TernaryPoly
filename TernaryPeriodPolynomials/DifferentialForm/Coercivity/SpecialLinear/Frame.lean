module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Cartan

@[expose] public section


/-! An orthogonal frame of the symmetric trace-zero tangent space, without square roots. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

/-- Orthogonal trace-metric frame of `p`. -/
def tangentFrame : Fin 5 → Mat := ![
  !![1, 0, 0; 0, -1, 0; 0, 0, 0],
  !![1, 0, 0; 0, 1, 0; 0, 0, -2],
  !![0, 1, 0; 1, 0, 0; 0, 0, 0],
  !![0, 0, 1; 0, 0, 0; 1, 0, 0],
  !![0, 0, 0; 0, 0, 1; 0, 1, 0]]

/-- Inverse squared lengths of the orthogonal tangent frame. -/
def tangentWeight : Fin 5 → ℝ := ![1/2, 1/6, 1/2, 1/2, 1/2]

theorem tangentWeight_pos (i : Fin 5) : 0 < tangentWeight i := by
  fin_cases i <;> norm_num [tangentWeight]

theorem tangentFrame_mem (i : Fin 5) : tangentFrame i ∈ symmetricTraceZero := by
  constructor
  · ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [tangentFrame]
  · fin_cases i <;> norm_num [tangentFrame, Matrix.trace, Fin.sum_univ_succ]

theorem tangentFrame_orthogonal (i j : Fin 5) :
    tangentWeight i * Matrix.trace (tangentFrame i * tangentFrame j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [tangentWeight, tangentFrame, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]

theorem tangentFrame_expansion (A : Mat) (hA : A ∈ symmetricTraceZero) :
    ∑ i : Fin 5, (tangentWeight i * Matrix.trace (tangentFrame i * A)) • tangentFrame i = A := by
  have hs : ∀ i j, A j i = A i j := fun i j => congrFun (congrFun hA.1 i) j
  have ht := hA.2
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_succ] at ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tangentWeight, tangentFrame, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_succ, hs] <;> norm_num at * <;> linarith

theorem tangentFrame_linearIndependent : LinearIndependent ℝ tangentFrame := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (fun A : Mat => tangentWeight i * Matrix.trace (tangentFrame i * A)) hc
  simp only [Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Finset.mul_sum, Matrix.trace_zero, mul_zero] at h
  have he : (∑ j : Fin 5, tangentWeight i * (c j * Matrix.trace (tangentFrame i * tangentFrame j))) = c i := by
    simp_rw [mul_left_comm (tangentWeight i), tangentFrame_orthogonal]
    simp
  exact he.symm.trans h

end TernaryPoly.SL3PolynomialCoercivity
