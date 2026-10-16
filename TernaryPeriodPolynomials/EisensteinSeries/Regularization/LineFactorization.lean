module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ParabolicFactorization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem lineParabolic_factorization {R : Type*} [CommRing R]
    (matrix : Adelic.GL3 R) (parabolic : InLineParabolic matrix) :
    ∃ (first second : R) (binary : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ),
      matrix = lineLevi scalar binary * lineUnipotent first second := by
  have inverse_parabolic := inLine_inv parabolic
  have inverse_first : matrix.val⁻¹ 1 0 = 0 := by simpa using inverse_parabolic.1
  have inverse_second : matrix.val⁻¹ 2 0 = 0 := by simpa using inverse_parabolic.2
  have corner : matrix.val 0 0 * matrix.inv 0 0 = 1 := by
    have entry := congrArg (fun value : Matrix (Fin 3) (Fin 3) R => value 0 0) matrix.val_inv
    simpa [Matrix.mul_apply, Fin.sum_univ_three, inverse_first, inverse_second] using entry
  have corner_as_inverse : matrix.val 0 0 * matrix.val⁻¹ 0 0 = 1 := by simpa using corner
  let scalar : Rˣ := ⟨matrix.val 0 0, matrix.inv 0 0, corner, by rw [mul_comm, corner]⟩
  let binary : GeneralLinearGroup (Fin 2) R :=
    ⟨!![matrix.val 1 1, matrix.val 1 2; matrix.val 2 1, matrix.val 2 2],
      !![matrix.inv 1 1, matrix.inv 1 2; matrix.inv 2 1, matrix.inv 2 2], by
        ext row column
        have entry := congrArg
          (fun value : Matrix (Fin 3) (Fin 3) R => value row.succ column.succ) matrix.val_inv
        fin_cases row <;> fin_cases column <;>
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
            parabolic.1, parabolic.2] using entry, by
        ext row column
        have entry := congrArg
          (fun value : Matrix (Fin 3) (Fin 3) R => value row.succ column.succ) matrix.inv_val
        fin_cases row <;> fin_cases column <;>
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
            inverse_first, inverse_second] using entry⟩
  refine ⟨scalar.inv * matrix.val 0 1, scalar.inv * matrix.val 0 2, binary, scalar, ?_⟩
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [lineLevi_val, lineUnipotent, upperUnipotent, binary, scalar,
      Matrix.mul_apply, Fin.sum_univ_three, parabolic.1, parabolic.2, ← mul_assoc, corner_as_inverse]

theorem lineLevi_split {R : Type*} [CommRing R]
    (scalar : Rˣ) (binary : GeneralLinearGroup (Fin 2) R) :
    lineLevi scalar binary = lineLevi scalar 1 * lineLevi 1 binary := by
  change lineLeviHom R (scalar, binary) = lineLeviHom R (scalar, 1) * lineLeviHom R (1, binary)
  rw [← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

theorem map_lineLevi {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (scalar : Rˣ) (binary : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.map ringMap (lineLevi scalar binary) =
      lineLevi (Units.map ringMap scalar) (GeneralLinearGroup.map ringMap binary) := by
  simp only [lineLevi, map_mul, map_inv, map_weyl, map_planeLevi]

theorem map_lineUnipotent {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (first second : R) :
    GeneralLinearGroup.map ringMap (lineUnipotent first second) =
      lineUnipotent (ringMap first) (ringMap second) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map, lineUnipotent, upperUnipotent, Matrix.map]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
