module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.FlagAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem det_planeLevi_general {R : Type*} [CommRing R]
    (binary : GeneralLinearGroup (Fin 2) R) (scalar : Rˣ) :
    GeneralLinearGroup.det (planeLevi binary scalar) = GeneralLinearGroup.det binary * scalar := by
  apply Units.ext
  change (planeBlock binary.val scalar.val).det = binary.val.det * scalar.val
  simp [planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem planeFlag_specialLinear_representative (flag : Flags .plane) :
    ∃ matrix : SpecialLinearGroup (Fin 3) ℤ,
      (QuotientGroup.mk (integerSpecialLinearRationalHom matrix) : Flags .plane) = flag := by
  obtain ⟨integer, represents⟩ := planeFlag_integral_representative flag
  let adjustment := planeLevi (1 : GeneralLinearGroup (Fin 2) ℤ) (GeneralLinearGroup.det integer)⁻¹
  have determinant : GeneralLinearGroup.det (integer * adjustment) = 1 := by
    rw [map_mul, det_planeLevi_general, map_one, one_mul, mul_inv_cancel]
  let special : SpecialLinearGroup (Fin 3) ℤ := ⟨(integer * adjustment).val,
    by exact congrArg Units.val determinant⟩
  have special_toGL : SpecialLinearGroup.toGL special = integer * adjustment := Units.ext rfl
  refine ⟨special, ?_⟩
  rw [integerSpecialLinearRationalHom, MonoidHom.comp_apply, special_toGL, map_mul]
  have same : (QuotientGroup.mk (integralRational integer * integralRational adjustment) : Flags .plane) =
      QuotientGroup.mk (integralRational integer) := by
    apply QuotientGroup.eq.mpr
    rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    apply inPlane_inv
    exact inPlane_map (Int.castRingHom ℚ) adjustment ⟨rfl, rfl⟩
  exact same.trans represents

noncomputable def planeFlagSpecialLinearRepresentative (flag : Flags .plane) : SpecialLinearGroup (Fin 3) ℤ :=
  Classical.choose (planeFlag_specialLinear_representative flag)

theorem planeFlagSpecialLinearRepresentative_spec (flag : Flags .plane) :
    (QuotientGroup.mk (integerSpecialLinearRationalHom (planeFlagSpecialLinearRepresentative flag)) : Flags .plane) = flag :=
  Classical.choose_spec (planeFlag_specialLinear_representative flag)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
