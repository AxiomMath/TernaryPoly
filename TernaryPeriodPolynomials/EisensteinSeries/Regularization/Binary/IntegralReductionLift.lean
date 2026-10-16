module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeBasic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def binaryIntegralRowReflection : GeneralLinearGroup (Fin 2) ℤ :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by decide, by decide⟩

def binaryIntegralRowRepresentatives : Fin 8 → SpecialLinearGroup (Fin 2) ℤ :=
  ![1, -1, ModularGroup.S, ModularGroup.S * ModularGroup.T, ModularGroup.S * ModularGroup.T ^ 2,
    -ModularGroup.S, -(ModularGroup.S * ModularGroup.T), -(ModularGroup.S * ModularGroup.T ^ 2)]

def binaryIntegralReductionRepresentative (sign : Fin 2) (shift : Fin 3) (row : Fin 8) :
    GeneralLinearGroup (Fin 2) ℤ :=
  binaryIntegralRowReflection ^ sign.val *
    SpecialLinearGroup.toGL (ModularGroup.T ^ shift.val * binaryIntegralRowRepresentatives row)

set_option maxRecDepth 4000 in
theorem binaryIntegralReduction_matrix_cover :
    ∀ matrix : Matrix (Fin 2) (Fin 2) (ZMod 3), matrix.det ≠ 0 →
      ∃ sign : Fin 2, ∃ shift : Fin 3, ∃ row : Fin 8,
        (GeneralLinearGroup.map (Int.castRingHom (ZMod 3))
          (binaryIntegralReductionRepresentative sign shift row)).val = matrix := by
  decide

theorem binaryIntegralReduction_surjective : Function.Surjective
    (GeneralLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod 3))) := by
  intro matrix
  obtain ⟨sign, shift, row, represents⟩ := binaryIntegralReduction_matrix_cover matrix.val matrix.det_ne_zero
  exact ⟨binaryIntegralReductionRepresentative sign shift row, Units.ext represents⟩

theorem binaryIntegerGL_map_map {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map ringMap (GeneralLinearGroup.map (Int.castRingHom R) matrix) =
      GeneralLinearGroup.map (Int.castRingHom S) matrix := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  exact map_intCast ringMap (matrix.val row column)

theorem binaryIntegral_integer_representative (matrix : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    ∃ integralMatrix : GeneralLinearGroup (Fin 2) ℤ,
      GeneralLinearGroup.map integralReduction (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integralMatrix) =
        GeneralLinearGroup.map integralReduction matrix := by
  obtain ⟨integralMatrix, represents⟩ := binaryIntegralReduction_surjective (GeneralLinearGroup.map integralReduction matrix)
  exact ⟨integralMatrix, (binaryIntegerGL_map_map integralReduction integralMatrix).trans represents⟩

theorem binaryIntegralRowReflection_real_det :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℝ) binaryIntegralRowReflection)) : ℝ) = -1 := by
  norm_num [GeneralLinearGroup.val_det_apply, binaryIntegralRowReflection, GeneralLinearGroup.map, Matrix.det_fin_two]

theorem binaryIntegralRowReflection_square : binaryIntegralRowReflection * binaryIntegralRowReflection = 1 := by
  decide

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
