module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.MatrixApartmentQuotient

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def UnitFrameSubdivision (weights : Fin 3 → ℤ) : Prop :=
  ∀ base : rationalLevel, normalizedMatrixClass base 1 =
    normalizedMatrixClass base ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 0 weights) +
    normalizedMatrixClass base ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 1 weights) +
    normalizedMatrixClass base ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 2 weights)

theorem unitFrameSubdivision_first : UnitFrameSubdivision ![1,0,0] := by
  intro base
  have first : (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 0 ![1,0,0] = 1 := by
    ext row column
    fin_cases row <;> fin_cases column <;> rfl
  have second : ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 1 ![1,0,0]).det = 0 := by
    norm_num [Matrix.det_fin_three, Matrix.one_apply, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have third : ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 2 ![1,0,0]).det = 0 := by
    norm_num [Matrix.det_fin_three, Matrix.one_apply, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  rw [first, normalizedMatrixClass_singular _ _ second, normalizedMatrixClass_singular _ _ third,
    add_zero, add_zero]

theorem unitFrameSubdivision_negative_sum : UnitFrameSubdivision ![-1,-1,0] := by
  intro base
  have first : (normalizedNorm * normalizedSwap).val.val =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 0 ![-1,-1,0] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [normalizedNorm, normalizedSwap, integralNormGenerator, integralSwapGenerator,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have second : (normalizedNorm * normalizedNorm * normalizedSwap).val.val =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 1 ![-1,-1,0] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [normalizedNorm, normalizedSwap, integralNormGenerator, integralSwapGenerator,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have third : ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 2 ![-1,-1,0]).det = 0 := by
    norm_num [Matrix.det_fin_three, Matrix.one_apply, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  rw [← first, ← second, normalizedMatrixClass_value, normalizedMatrixClass_value,
    normalizedMatrixClass_singular _ _ third, add_zero, frameChangeClass_swap, frameChangeClass_swap]
  change normalizedMatrixClass base (1 : normalizedFrameChanges).val.val = _
  rw [normalizedMatrixClass_value]
  have norm := frameChangeClass_norm base 1
  simp only [one_mul] at norm
  calc
    frameChangeClass base 1 =
        (frameChangeClass base 1 + frameChangeClass base normalizedNorm +
          frameChangeClass base (normalizedNorm * normalizedNorm)) -
          frameChangeClass base normalizedNorm - frameChangeClass base (normalizedNorm * normalizedNorm) := by abel
    _ = _ := by rw [norm]; abel

theorem unitFrameSubdivision_square : UnitFrameSubdivision ![1,1,-1] := by
  intro base
  have first : (squareBCD * normalizedCyclic * normalizedCyclic).val.val =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 0 ![1,1,-1] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [squareBCD, normalizedCyclic, integralCyclicGenerator,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have second : (squareACD * normalizedCyclic * normalizedSwap * normalizedCyclic * normalizedCyclic).val.val =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 1 ![1,1,-1] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [squareACD, normalizedCyclic, normalizedSwap, integralCyclicGenerator,
        integralSwapGenerator, Matrix.mul_apply, Fin.sum_univ_three, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have third : squareABD.val.val =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 2 ![1,1,-1] := by
    ext row column
    fin_cases row <;> fin_cases column <;> rfl
  rw [← first, ← second, ← third, normalizedMatrixClass_value, normalizedMatrixClass_value,
    normalizedMatrixClass_value]
  simp only [frameChangeClass_cyclic, frameChangeClass_swap]
  change normalizedMatrixClass base (1 : normalizedFrameChanges).val.val = _
  rw [normalizedMatrixClass_value]
  simpa only [sub_eq_add_neg] using (sub_eq_zero.mp (frameChangeClass_square base)).symm

def rotateWeights (weights : Fin 3 → ℤ) : Fin 3 → ℤ := ![weights 2, weights 0, weights 1]

theorem rotate_update_zero (weights : Fin 3 → ℤ) :
    integralCyclicGenerator.val * (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 0 weights =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 1 (rotateWeights weights) * integralCyclicGenerator.val := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [integralCyclicGenerator, rotateWeights, Matrix.mul_apply, Fin.sum_univ_three, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rotate_update_one (weights : Fin 3 → ℤ) :
    integralCyclicGenerator.val * (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 1 weights =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 2 (rotateWeights weights) * integralCyclicGenerator.val := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [integralCyclicGenerator, rotateWeights, Matrix.mul_apply, Fin.sum_univ_three, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rotate_update_two (weights : Fin 3 → ℤ) :
    integralCyclicGenerator.val * (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 2 weights =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 0 (rotateWeights weights) * integralCyclicGenerator.val := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [integralCyclicGenerator, rotateWeights, Matrix.mul_apply, Fin.sum_univ_three, Matrix.updateCol_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem UnitFrameSubdivision.rotate {weights : Fin 3 → ℤ} (subdivision : UnitFrameSubdivision weights) :
    UnitFrameSubdivision (rotateWeights weights) := by
  intro base
  have rotated := subdivision (base * normalizedFrameChangeMap normalizedCyclic)
  rw [← normalizedMatrixClass_left_mul base normalizedCyclic 1,
    ← normalizedMatrixClass_left_mul base normalizedCyclic ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 0 weights),
    ← normalizedMatrixClass_left_mul base normalizedCyclic ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 1 weights),
    ← normalizedMatrixClass_left_mul base normalizedCyclic ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 2 weights)] at rotated
  change normalizedMatrixClass base (integralCyclicGenerator.val * 1) = _ at rotated
  rw [show normalizedCyclic.val.val = integralCyclicGenerator.val from rfl] at rotated
  rw [rotate_update_zero, rotate_update_one, rotate_update_two] at rotated
  simp only [normalizedMatrixClass_right_cyclic] at rotated
  have identity := normalizedMatrixClass_right_cyclic base 1
  rw [Matrix.one_mul] at identity
  rw [Matrix.mul_one, identity] at rotated
  rw [rotated]
  abel

theorem bounded_normalized_triple_cases (first second third : ℤ)
    (first_bound : |first| ≤ 1) (second_bound : |second| ≤ 1) (third_bound : |third| ≤ 1)
    (normalized : ((first + second + third : ℤ) : ZMod 3) = 1) :
    (![first,second,third] : Fin 3 → ℤ) = ![1,0,0] ∨
    (![first,second,third] : Fin 3 → ℤ) = ![0,1,0] ∨
    (![first,second,third] : Fin 3 → ℤ) = ![0,0,1] ∨
    (![first,second,third] : Fin 3 → ℤ) = ![-1,-1,0] ∨
    (![first,second,third] : Fin 3 → ℤ) = ![0,-1,-1] ∨
    (![first,second,third] : Fin 3 → ℤ) = ![-1,0,-1] ∨
    (![first,second,third] : Fin 3 → ℤ) = ![1,1,-1] ∨
    (![first,second,third] : Fin 3 → ℤ) = ![-1,1,1] ∨
    (![first,second,third] : Fin 3 → ℤ) = ![1,-1,1] := by
  obtain ⟨first_lower, first_upper⟩ := abs_le.mp first_bound
  obtain ⟨second_lower, second_upper⟩ := abs_le.mp second_bound
  obtain ⟨third_lower, third_upper⟩ := abs_le.mp third_bound
  interval_cases first <;> interval_cases second <;> interval_cases third <;>
    first | exact absurd normalized (by decide) | decide

/-- Every normalized insertion with unit or zero replacement determinants
satisfies the subdivision identity in the presented apartment module. -/
theorem unitFrameSubdivision_of_bounded (weights : Fin 3 → ℤ)
    (bounded : ∀ column, |weights column| ≤ 1)
    (normalized : ((weights 0 + weights 1 + weights 2 : ℤ) : ZMod 3) = 1) :
    UnitFrameSubdivision weights := by
  have cases := bounded_normalized_triple_cases (weights 0) (weights 1) (weights 2)
    (bounded 0) (bounded 1) (bounded 2) normalized
  have expanded : weights = ![weights 0,weights 1,weights 2] := by
    ext index
    fin_cases index <;> rfl
  rw [← expanded] at cases
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact unitFrameSubdivision_first
  · exact unitFrameSubdivision_first.rotate
  · exact unitFrameSubdivision_first.rotate.rotate
  · exact unitFrameSubdivision_negative_sum
  · exact unitFrameSubdivision_negative_sum.rotate
  · exact unitFrameSubdivision_negative_sum.rotate.rotate
  · exact unitFrameSubdivision_square
  · exact unitFrameSubdivision_square.rotate
  · exact unitFrameSubdivision_square.rotate.rotate

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
