module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.CoefficientCasimir

@[expose] public section


/-! Exact tangent-frame commutator table in the skew frame. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

def tangentCommutatorCoordinates : Fin 5 → Fin 5 → Fin 3 → ℝ := ![
  ![![0, 0, 0], ![0, 0, 0], ![2, 0, 0], ![0, 1, 0], ![0, 0, -1]],
  ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, 0], ![0, 0, 3]],
  ![![-2, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 1], ![0, 1, 0]],
  ![![0, -1, 0], ![0, -3, 0], ![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
  ![![0, 0, 1], ![0, 0, -3], ![0, -1, 0], ![-1, 0, 0], ![0, 0, 0]]]

theorem tangentFrame_commutator_0 (j : Fin 5) :
    tangentFrame 0 * tangentFrame j - tangentFrame j * tangentFrame 0 =
      ∑ k : Fin 3, tangentCommutatorCoordinates 0 j k • skewFrame k := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [tangentFrame, tangentCommutatorCoordinates, skewFrame,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.cons_val, Fin.sum_univ_succ]

theorem tangentFrame_commutator_1 (j : Fin 5) :
    tangentFrame 1 * tangentFrame j - tangentFrame j * tangentFrame 1 =
      ∑ k : Fin 3, tangentCommutatorCoordinates 1 j k • skewFrame k := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [tangentFrame, tangentCommutatorCoordinates, skewFrame,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.cons_val, Fin.sum_univ_succ]

theorem tangentFrame_commutator_2 (j : Fin 5) :
    tangentFrame (⟨2, by decide⟩ : Fin 5) * tangentFrame j - tangentFrame j * tangentFrame (⟨2, by decide⟩ : Fin 5) =
      ∑ k : Fin 3, tangentCommutatorCoordinates (⟨2, by decide⟩ : Fin 5) j k • skewFrame k := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [tangentFrame, tangentCommutatorCoordinates, skewFrame,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.cons_val, Fin.sum_univ_succ]

theorem tangentFrame_commutator_3 (j : Fin 5) :
    tangentFrame (⟨3, by decide⟩ : Fin 5) * tangentFrame j - tangentFrame j * tangentFrame (⟨3, by decide⟩ : Fin 5) =
      ∑ k : Fin 3, tangentCommutatorCoordinates (⟨3, by decide⟩ : Fin 5) j k • skewFrame k := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [tangentFrame, tangentCommutatorCoordinates, skewFrame,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.cons_val, Fin.sum_univ_succ]

theorem tangentFrame_commutator_4 (j : Fin 5) :
    tangentFrame (⟨4, by decide⟩ : Fin 5) * tangentFrame j - tangentFrame j * tangentFrame (⟨4, by decide⟩ : Fin 5) =
      ∑ k : Fin 3, tangentCommutatorCoordinates (⟨4, by decide⟩ : Fin 5) j k • skewFrame k := by
  fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [tangentFrame, tangentCommutatorCoordinates, skewFrame,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.cons_val, Fin.sum_univ_succ]

theorem tangentFrame_commutator (i j : Fin 5) :
    tangentFrame i * tangentFrame j - tangentFrame j * tangentFrame i =
      ∑ k : Fin 3, tangentCommutatorCoordinates i j k • skewFrame k := by
  fin_cases i
  · exact tangentFrame_commutator_0 j
  · exact tangentFrame_commutator_1 j
  · exact tangentFrame_commutator_2 j
  · exact tangentFrame_commutator_3 j
  · exact tangentFrame_commutator_4 j

theorem infinitesimal_tangent_commutator (i j : Fin 5) (p : Poly) :
    infinitesimal (tangentFrame i * tangentFrame j - tangentFrame j * tangentFrame i) p =
      ∑ k : Fin 3, tangentCommutatorCoordinates i j k • infinitesimal (skewFrame k) p := by
  rw [tangentFrame_commutator]
  simp [Fin.sum_univ_succ, infinitesimal_add, infinitesimal_smul]

end TernaryPoly.SL3PolynomialCoercivity
