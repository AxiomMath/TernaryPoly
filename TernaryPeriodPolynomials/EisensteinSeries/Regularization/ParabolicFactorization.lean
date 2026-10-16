module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem planeParabolic_factorization {R : Type*} [CommRing R]
    (matrix : Adelic.GL3 R) (parabolic : InPlaneParabolic matrix) :
    ∃ (first second : R) (binary : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ),
      matrix = planeUnipotent first second * planeLevi binary scalar := by
  have inverse_parabolic := inPlane_inv parabolic
  have inverse_first : matrix.val⁻¹ 2 0 = 0 := by
    simpa using inverse_parabolic.1
  have inverse_second : matrix.val⁻¹ 2 1 = 0 := by
    simpa using inverse_parabolic.2
  have corner : matrix.val 2 2 * matrix.inv 2 2 = 1 := by
    have entry := congrArg (fun value : Matrix (Fin 3) (Fin 3) R => value 2 2)
      matrix.val_inv
    simpa [Matrix.mul_apply, Fin.sum_univ_three, parabolic.1, parabolic.2] using entry
  have reverse_corner : matrix.val⁻¹ 2 2 * matrix.val 2 2 = 1 := by
    simpa [mul_comm] using corner
  let scalar : Rˣ := ⟨matrix.val 2 2, matrix.inv 2 2, corner, by
    rw [mul_comm, corner]⟩
  let binary : GeneralLinearGroup (Fin 2) R :=
    ⟨!![matrix.val 0 0, matrix.val 0 1; matrix.val 1 0, matrix.val 1 1],
      !![matrix.inv 0 0, matrix.inv 0 1; matrix.inv 1 0, matrix.inv 1 1], by
        ext row column
        have entry := congrArg
          (fun value : Matrix (Fin 3) (Fin 3) R => value row.castSucc column.castSucc)
          matrix.val_inv
        fin_cases row <;> fin_cases column <;>
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
            inverse_first, inverse_second] using entry, by
        ext row column
        have entry := congrArg
          (fun value : Matrix (Fin 3) (Fin 3) R => value row.castSucc column.castSucc)
          matrix.inv_val
        fin_cases row <;> fin_cases column <;>
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
            parabolic.1, parabolic.2] using entry⟩
  refine ⟨matrix.val 0 2 * scalar.inv, matrix.val 1 2 * scalar.inv,
    binary, scalar, ?_⟩
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeUnipotent, planeLevi, planeBlock, binary, scalar,
      Matrix.mul_apply, Fin.sum_univ_three, parabolic.1, parabolic.2,
      mul_assoc, reverse_corner]

theorem map_planeLevi {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (binary : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ) :
    GeneralLinearGroup.map ringMap (planeLevi binary scalar) =
      planeLevi (GeneralLinearGroup.map ringMap binary) (Units.map ringMap scalar) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map, planeLevi, planeBlock, Matrix.map]

theorem map_planeUnipotent {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (first second : R) :
    GeneralLinearGroup.map ringMap (planeUnipotent first second) =
      planeUnipotent (ringMap first) (ringMap second) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map, planeUnipotent, Matrix.map]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
