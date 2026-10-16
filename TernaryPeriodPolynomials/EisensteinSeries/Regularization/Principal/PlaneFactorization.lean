module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.PlaneSlice
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearPlaneUnipotent

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem principalIntegerSpecialLinear_entry (matrix : SpecialLinearGroup (Fin 3) ℤ)
    (member : matrix ∈ principalIntegerSpecialLinear) (row column : Fin 3) :
    (matrix.val row column : ZMod 3) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) row column := by
  change integerSpecialLinearReduction matrix = 1 at member
  exact congrArg (fun value : SpecialLinearGroup (Fin 3) (ZMod 3) => value.val row column) member

theorem principalIntegerPlane_corner_one (matrix : SpecialLinearGroup (Fin 3) ℤ)
    (member : matrix ∈ principalIntegerSpecialLinear)
    (first_zero : matrix.val 2 0 = 0) (second_zero : matrix.val 2 1 = 0) :
    matrix.val 2 2 = 1 := by
  have determinant : (matrix.val 0 0 * matrix.val 1 1 - matrix.val 0 1 * matrix.val 1 0) *
      matrix.val 2 2 = 1 := by
    have determinant := matrix.property
    simp only [Matrix.det_fin_three, first_zero, second_zero, mul_zero, add_zero,
      sub_zero] at determinant
    nlinarith [determinant]
  have unit : IsUnit (matrix.val 2 2) :=
    ⟨⟨matrix.val 2 2, matrix.val 0 0 * matrix.val 1 1 - matrix.val 0 1 * matrix.val 1 0,
      by nlinarith [determinant], determinant⟩, rfl⟩
  rcases Int.isUnit_iff.mp unit with one | negative
  · exact one
  · have reduction := principalIntegerSpecialLinear_entry matrix member 2 2
    rw [negative] at reduction
    exact False.elim ((by decide : (-1 : ZMod 3) ≠ 1) (by simpa only [Int.cast_neg, Int.cast_one,
      Matrix.one_apply_eq] using reduction))

theorem principalIntegerPlaneUnipotent_mem (first second : ℤ) :
    specialLinearPlaneUnipotent (3 * first) (3 * second) ∈ principalIntegerSpecialLinear := by
  change SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) _ = 1
  rw [specialLinearPlaneUnipotent_map]
  simp only [map_mul, map_ofNat, show (3 : ZMod 3) = 0 from by decide, zero_mul]
  exact specialLinearPlaneUnipotent_zero (R := ZMod 3)

theorem specialLinearPlaneLevi_map {R S : Type*} [CommRing R] [CommRing S]
    (map : R →+* S) (binary : SpecialLinearGroup (Fin 2) R) :
    SpecialLinearGroup.map map (specialLinearPlaneLevi binary) =
      specialLinearPlaneLevi (SpecialLinearGroup.map map binary) := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [specialLinearPlaneLevi, planeBlock, SpecialLinearGroup.map]

theorem principalIntegerPlane_factorization (matrix : SpecialLinearGroup (Fin 3) ℤ)
    (member : matrix ∈ principalIntegerSpecialLinear)
    (first_zero : matrix.val 2 0 = 0) (second_zero : matrix.val 2 1 = 0) :
    ∃ first second : ℤ, ∃ binary : SpecialLinearGroup (Fin 2) ℤ,
      matrix = specialLinearPlaneUnipotent (3 * first) (3 * second) * specialLinearPlaneLevi binary ∧
        specialLinearPlaneLevi binary ∈ principalIntegerSpecialLinear := by
  have corner := principalIntegerPlane_corner_one matrix member first_zero second_zero
  have first_multiple : (3 : ℤ) ∣ matrix.val 0 2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    simpa using principalIntegerSpecialLinear_entry matrix member 0 2
  have second_multiple : (3 : ℤ) ∣ matrix.val 1 2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    simpa using principalIntegerSpecialLinear_entry matrix member 1 2
  obtain ⟨first, first_eq⟩ := first_multiple
  obtain ⟨second, second_eq⟩ := second_multiple
  let binary : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![matrix.val 0 0, matrix.val 0 1; matrix.val 1 0, matrix.val 1 1], by
      have determinant := matrix.property
      rw [Matrix.det_fin_three, first_zero, second_zero, corner] at determinant
      rw [Matrix.det_fin_two]
      change matrix.val 0 0 * matrix.val 1 1 - matrix.val 0 1 * matrix.val 1 0 = 1
      simpa only [mul_one, mul_zero, add_zero, sub_zero] using determinant⟩
  have factorization : matrix =
      specialLinearPlaneUnipotent (3 * first) (3 * second) * specialLinearPlaneLevi binary := by
    apply Subtype.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [specialLinearPlaneUnipotent, specialLinearPlaneLevi, planeBlock, binary,
        Matrix.mul_apply, Fin.sum_univ_three, first_zero, second_zero, corner, first_eq, second_eq]
  refine ⟨first, second, binary, factorization, ?_⟩
  have member' := principalIntegerSpecialLinear.mul_mem
    (principalIntegerSpecialLinear.inv_mem (principalIntegerPlaneUnipotent_mem first second)) member
  rw [factorization, inv_mul_cancel_left] at member'
  exact member'

def principalRealPlaneParabolic : Subgroup (SpecialLinearGroup (Fin 3) ℝ) :=
  principalRealSpecialLinear ⊓ (planeParabolic ℝ).comap SpecialLinearGroup.toGL

theorem principalRealPlaneParabolic_factorization (element : principalRealPlaneParabolic) :
    ∃ first second : ℤ, ∃ levi : principalRealPlaneLevi,
      element.val = realSpecialPlane (3 * (first : ℝ)) (3 * (second : ℝ)) * levi.val := by
  obtain ⟨matrix, principal, represents⟩ := element.property.1
  have first_zero : matrix.val 2 0 = 0 := by
    have zero := element.property.2.1
    rw [← represents] at zero
    change (matrix.val 2 0 : ℝ) = 0 at zero
    exact_mod_cast zero
  have second_zero : matrix.val 2 1 = 0 := by
    have zero := element.property.2.2
    rw [← represents] at zero
    change (matrix.val 2 1 : ℝ) = 0 at zero
    exact_mod_cast zero
  obtain ⟨first, second, binary, factorization, levi_principal⟩ :=
    principalIntegerPlane_factorization matrix principal first_zero second_zero
  let realLevi := SpecialLinearGroup.map (Int.castRingHom ℝ) (specialLinearPlaneLevi binary)
  have levi_member : realLevi ∈ principalRealPlaneLevi := by
    refine ⟨⟨specialLinearPlaneLevi binary, levi_principal, rfl⟩, ?_⟩
    exact ⟨SpecialLinearGroup.map (Int.castRingHom ℝ) binary, (specialLinearPlaneLevi_map _ _).symm⟩
  refine ⟨first, second, ⟨realLevi, levi_member⟩, ?_⟩
  rw [← represents, factorization, map_mul, specialLinearPlaneUnipotent_map,
    specialLinearPlaneUnipotent_real]
  norm_cast

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
