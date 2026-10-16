module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.FixedVanishing

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def binaryReducedRowStabilizer : Subgroup (GeneralLinearGroup (Fin 2) (ZMod 3)) where
  carrier := {matrix | (Pi.single 1 1 : Fin 2 → ZMod 3) ᵥ* matrix.val = Pi.single 1 1}
  one_mem' := by
    change (Pi.single 1 1 : Fin 2 → ZMod 3) ᵥ* (1 : GeneralLinearGroup (Fin 2) (ZMod 3)).val = _
    rw [GeneralLinearGroup.coe_one, vecMul_one]
  mul_mem' {first second} first_fixed second_fixed := by
    change (Pi.single 1 1 : Fin 2 → ZMod 3) ᵥ* (first.val * second.val) = _
    rw [← vecMul_vecMul, first_fixed, second_fixed]
  inv_mem' {matrix} fixed := by
    change (Pi.single 1 1 : Fin 2 → ZMod 3) ᵥ* matrix⁻¹.val = _
    have identity := congrArg (fun row => row ᵥ* (matrix⁻¹).val) fixed
    simpa only [vecMul_vecMul, ← GeneralLinearGroup.coe_mul, mul_inv_cancel,
      GeneralLinearGroup.coe_one, vecMul_one] using identity.symm

noncomputable def binaryRowLevel : Subgroup BinaryFiniteGL :=
  (binaryReducedRowStabilizer.comap (GeneralLinearGroup.map integralReduction)).map
    (GeneralLinearGroup.map integralEmbedding)

theorem binaryReducedRowStabilizer_mem (matrix : GeneralLinearGroup (Fin 2) (ZMod 3)) :
    matrix ∈ binaryReducedRowStabilizer ↔ matrix.val 1 0 = 0 ∧ matrix.val 1 1 = 1 := by
  change ((Pi.single 1 1 : Fin 2 → ZMod 3) ᵥ* matrix.val = Pi.single 1 1) ↔ _
  simp [funext_iff, Fin.forall_fin_two, Pi.single_apply]

theorem binaryPrincipalLevel_le_rowLevel : binaryPrincipalLevel ≤ binaryRowLevel := by
  rintro matrix ⟨integralMatrix, reduced, represents⟩
  refine ⟨integralMatrix, ?_, represents⟩
  change GeneralLinearGroup.map integralReduction integralMatrix ∈ binaryReducedRowStabilizer
  rw [show GeneralLinearGroup.map integralReduction integralMatrix = 1 from reduced]
  exact Subgroup.one_mem _

theorem binaryRowLevel_gammaOneThree (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (member : matrix ∈ CongruenceSubgroup.Gamma1 3) :
    SpecialLinearGroup.mapGL FiniteAdeles matrix ∈ binaryRowLevel := by
  refine ⟨SpecialLinearGroup.mapGL IntegralAdeles matrix, ?_, binaryIntegral_mapGL_map integralEmbedding matrix⟩
  change GeneralLinearGroup.map integralReduction (SpecialLinearGroup.mapGL IntegralAdeles matrix) ∈ binaryReducedRowStabilizer
  rw [binaryIntegral_mapGL_map, binaryReducedRowStabilizer_mem, binaryIntegral_mapGL_entry, binaryIntegral_mapGL_entry]
  exact ⟨(CongruenceSubgroup.Gamma1_mem 3 matrix).mp member |>.2.2,
    (CongruenceSubgroup.Gamma1_mem 3 matrix).mp member |>.2.1⟩

theorem binaryRowLevel_reflection :
    GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) binaryIntegralRowReflection ∈ binaryRowLevel := by
  refine ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) binaryIntegralRowReflection, ?_,
    binaryIntegerGL_map_map integralEmbedding binaryIntegralRowReflection⟩
  change GeneralLinearGroup.map integralReduction
    (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) binaryIntegralRowReflection) ∈ binaryReducedRowStabilizer
  rw [binaryIntegerGL_map_map, binaryReducedRowStabilizer_mem]
  norm_num [GeneralLinearGroup.map, binaryIntegralRowReflection]

theorem cohomological_small_degree_rowLevel_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (small : degree < 3) (vector : cuspFiniteFixedSubmodule cusp binaryRowLevel) : vector.val = 0 :=
  cohomological_small_degree_fixed_zero cohomological small binaryRowLevel binaryPrincipalLevel_le_rowLevel
    binaryRowLevel_gammaOneThree binaryRowLevel_reflection vector

theorem binaryIntegralRowRepresentatives_cover :
    ∀ row : Fin 2 → ZMod 3, row ≠ 0 → ∃ index : Fin 8,
      (SpecialLinearGroup.mapGL (ZMod 3) (binaryIntegralRowRepresentatives index)).val 1 = row := by
  decide

theorem binaryIntegralRowRepresentatives_reduce (row : Fin 2 → ZMod 3) :
    ∃ matrix : SpecialLinearGroup (Fin 2) ℤ,
      (row ᵥ* (SpecialLinearGroup.mapGL (ZMod 3) matrix)⁻¹.val) 0 = 0 := by
  by_cases zero : row = 0
  · exact ⟨1, by simp [zero]⟩
  · obtain ⟨index, represents⟩ := binaryIntegralRowRepresentatives_cover row zero
    refine ⟨binaryIntegralRowRepresentatives index, ?_⟩
    have identity : row ᵥ* (SpecialLinearGroup.mapGL (ZMod 3) (binaryIntegralRowRepresentatives index))⁻¹.val =
        Pi.single 1 1 := by
      have row_eq : row = (Pi.single 1 1 : Fin 2 → ZMod 3) ᵥ*
          (SpecialLinearGroup.mapGL (ZMod 3) (binaryIntegralRowRepresentatives index)).val := by
        rw [← represents]
        ext column
        simp [Matrix.vecMul, dotProduct, Pi.single_apply]
      rw [row_eq, vecMul_vecMul, ← GeneralLinearGroup.coe_mul, mul_inv_cancel, GeneralLinearGroup.coe_one, vecMul_one]
    rw [identity]
    simp

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
