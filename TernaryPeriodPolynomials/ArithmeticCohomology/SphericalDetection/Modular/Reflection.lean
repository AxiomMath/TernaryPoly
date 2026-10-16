module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CuspCohomologyNonvanishing

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Conjugation by `diag(1,-1)` on the integral special linear group. -/
def modularReflection : SpecialLinearGroup (Fin 2) ℤ →* SpecialLinearGroup (Fin 2) ℤ where
  toFun matrix := ⟨!![matrix.val 0 0, -matrix.val 0 1; -matrix.val 1 0, matrix.val 1 1], by
    have determinant := matrix.property
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      neg_mul_neg]
    simpa only [Matrix.det_fin_two] using determinant⟩
  map_one' := by
    apply Subtype.ext
    ext row column
    fin_cases row <;> fin_cases column <;> simp
  map_mul' first second := by
    apply Subtype.ext
    change !![(first.val * second.val) 0 0, -(first.val * second.val) 0 1;
      -(first.val * second.val) 1 0, (first.val * second.val) 1 1] =
        !![first.val 0 0, -first.val 0 1; -first.val 1 0, first.val 1 1] *
          !![second.val 0 0, -second.val 0 1; -second.val 1 0, second.val 1 1]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem modularReflection_apply (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    (modularReflection matrix).val =
      !![matrix.val 0 0, -matrix.val 0 1; -matrix.val 1 0, matrix.val 1 1] := rfl

theorem modularReflection_involutive : Function.Involutive modularReflection := by
  intro matrix
  apply Subtype.ext
  rw [modularReflection_apply, modularReflection_apply]
  ext row column
  fin_cases row <;> fin_cases column <;> simp

theorem modularReflection_S : modularReflection ModularGroup.S = ModularGroup.S⁻¹ := by
  rw [SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  rfl

theorem modularReflection_T : modularReflection ModularGroup.T = ModularGroup.T⁻¹ := by
  rw [SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  rfl

theorem binaryParityReflection_involutive (degree : ℕ) :
    Function.Involutive (binaryParityReflection degree) := by
  intro polynomial
  apply (binaryStandardBasis degree).ext_elem
  intro position
  change (binaryStandardBasis degree).coord position
    (binaryParityReflection degree (binaryParityReflection degree polynomial)) =
      (binaryStandardBasis degree).coord position polynomial
  rw [binaryParityReflection_coord, binaryParityReflection_coord, ← mul_assoc, ← pow_add]
  have exponent_even : Even ((degree - position.val) + (degree - position.val)) := ⟨_, rfl⟩
  rw [exponent_even.neg_one_pow, one_mul]

theorem binaryParityReflection_modular_intertwines (degree : ℕ) (twist : ℤ)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (polynomial : Binary.HomogeneousPoly degree) :
    binaryParityReflection degree
      ((modularBinaryRep degree twist).ρ (modularReflection matrix) polynomial) =
        (modularBinaryRep degree twist).ρ matrix (binaryParityReflection degree polynomial) := by
  apply Subtype.ext
  change Binary.substitute !![1, 0; 0, -1]
      (((arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL (modularReflection matrix)) polynomial).val) =
    (((arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL matrix))
      (binaryParityReflection degree polynomial)).val
  rw [arithmeticBinaryRep_specialLinear_coe, arithmeticBinaryRep_specialLinear_coe]
  change Binary.substitute !![1, 0; 0, -1]
      (Binary.substitute (((modularReflection matrix)⁻¹).val.map (Int.castRingHom ℂ)) polynomial.val) =
    Binary.substitute ((matrix⁻¹).val.map (Int.castRingHom ℂ))
      (Binary.substitute !![1, 0; 0, -1] polynomial.val)
  change ((Binary.substitute !![1, 0; 0, -1]).comp
      (Binary.substitute (((modularReflection matrix)⁻¹).val.map (Int.castRingHom ℂ)))) polynomial.val =
    ((Binary.substitute ((matrix⁻¹).val.map (Int.castRingHom ℂ))).comp
      (Binary.substitute !![1, 0; 0, -1])) polynomial.val
  rw [Binary.substitute_comp, Binary.substitute_comp]
  have matrices : (((modularReflection matrix)⁻¹).val.map (Int.castRingHom ℂ)) * !![1, 0; 0, -1] =
      !![1, 0; 0, -1] * ((matrix⁻¹).val.map (Int.castRingHom ℂ)) := by
    rw [← map_inv, modularReflection_apply]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [matrices]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
