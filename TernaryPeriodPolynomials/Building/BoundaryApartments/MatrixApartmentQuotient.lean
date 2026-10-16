module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.SquareRelation

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

/-- The class of a normalized unimodular change matrix, and zero for matrices
which do not represent such a change. -/
def normalizedMatrixClass (base : rationalLevel) (matrix : Matrix (Fin 3) (Fin 3) ℤ) : ApartmentQuotient := by
  classical
  exact if represented : ∃ change : normalizedFrameChanges, change.val.val = matrix then
    frameChangeClass base (Classical.choose represented) else 0

theorem normalizedMatrixClass_value (base : rationalLevel) (change : normalizedFrameChanges) :
    normalizedMatrixClass base change.val.val = frameChangeClass base change := by
  rw [normalizedMatrixClass, dite_eq_left ⟨change, rfl⟩]
  congr 1
  apply Subtype.ext
  apply Units.ext
  exact Classical.choose_spec (show ∃ candidate : normalizedFrameChanges,
    candidate.val.val = change.val.val from ⟨change, rfl⟩)

theorem normalizedMatrixClass_eq (base : rationalLevel) (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (change : normalizedFrameChanges) (entries : change.val.val = matrix) :
    normalizedMatrixClass base matrix = frameChangeClass base change := by
  rw [← entries, normalizedMatrixClass_value]

theorem normalizedMatrixClass_singular (base : rationalLevel) (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (singular : matrix.det = 0) : normalizedMatrixClass base matrix = 0 := by
  have absent : ¬∃ change : normalizedFrameChanges, change.val.val = matrix := by
    rintro ⟨change, entries⟩
    have nonzero := ((Matrix.isUnit_iff_isUnit_det change.val.val).mp change.val.isUnit).ne_zero
    exact nonzero (entries ▸ singular)
  rw [normalizedMatrixClass, dite_eq_right absent]

theorem frameChangeClass_mul (base : rationalLevel) (first second : normalizedFrameChanges) :
    frameChangeClass base (first * second) =
      frameChangeClass (base * normalizedFrameChangeMap first) second := by
  simp only [frameChangeClass, map_mul, mul_assoc]

theorem normalizedMatrixClass_left_mul (base : rationalLevel) (change : normalizedFrameChanges)
    (matrix : Matrix (Fin 3) (Fin 3) ℤ) :
    normalizedMatrixClass base (change.val.val * matrix) =
      normalizedMatrixClass (base * normalizedFrameChangeMap change) matrix := by
  by_cases represented : ∃ candidate : normalizedFrameChanges, candidate.val.val = matrix
  · obtain ⟨candidate, rfl⟩ := represented
    change normalizedMatrixClass base (change * candidate).val.val = _
    rw [normalizedMatrixClass_value, normalizedMatrixClass_value, frameChangeClass_mul]
  · have absent : ¬∃ candidate : normalizedFrameChanges, candidate.val.val = change.val.val * matrix := by
      rintro ⟨candidate, entries⟩
      apply represented
      refine ⟨change⁻¹ * candidate, ?_⟩
      change change.val.inv * candidate.val.val = matrix
      rw [entries, ← Matrix.mul_assoc, change.val.inv_val, Matrix.one_mul]
    rw [normalizedMatrixClass, dite_eq_right absent, normalizedMatrixClass, dite_eq_right represented]

theorem normalizedMatrixClass_right_cyclic (base : rationalLevel)
    (matrix : Matrix (Fin 3) (Fin 3) ℤ) :
    normalizedMatrixClass base (matrix * integralCyclicGenerator.val) = normalizedMatrixClass base matrix := by
  by_cases represented : ∃ candidate : normalizedFrameChanges, candidate.val.val = matrix
  · obtain ⟨candidate, rfl⟩ := represented
    change normalizedMatrixClass base (candidate * normalizedCyclic).val.val = _
    rw [normalizedMatrixClass_value, normalizedMatrixClass_value, frameChangeClass_cyclic]
  · have absent : ¬∃ candidate : normalizedFrameChanges,
        candidate.val.val = matrix * integralCyclicGenerator.val := by
      rintro ⟨candidate, entries⟩
      apply represented
      refine ⟨candidate * normalizedCyclic⁻¹, ?_⟩
      change candidate.val.val * integralCyclicGenerator.inv = matrix
      rw [entries, Matrix.mul_assoc, integralCyclicGenerator.val_inv, Matrix.mul_one]
    rw [normalizedMatrixClass, dite_eq_right absent, normalizedMatrixClass, dite_eq_right represented]

theorem normalizedMatrixClass_right_swap (base : rationalLevel)
    (matrix : Matrix (Fin 3) (Fin 3) ℤ) :
    normalizedMatrixClass base (matrix * integralSwapGenerator.val) = -normalizedMatrixClass base matrix := by
  by_cases represented : ∃ candidate : normalizedFrameChanges, candidate.val.val = matrix
  · obtain ⟨candidate, rfl⟩ := represented
    change normalizedMatrixClass base (candidate * normalizedSwap).val.val = _
    rw [normalizedMatrixClass_value, normalizedMatrixClass_value, frameChangeClass_swap]
  · have absent : ¬∃ candidate : normalizedFrameChanges,
        candidate.val.val = matrix * integralSwapGenerator.val := by
      rintro ⟨candidate, entries⟩
      apply represented
      refine ⟨candidate * normalizedSwap⁻¹, ?_⟩
      change candidate.val.val * integralSwapGenerator.inv = matrix
      rw [entries, Matrix.mul_assoc, integralSwapGenerator.val_inv, Matrix.mul_one]
    rw [normalizedMatrixClass, dite_eq_right absent, normalizedMatrixClass, dite_eq_right represented, neg_zero]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
