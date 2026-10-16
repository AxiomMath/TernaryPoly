module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.RowLevel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem reduced_row_planeLevi_fixed (row : Fin 3 → ZMod 3) (zero : row 0 = 0)
    (binary : GeneralLinearGroup (Fin 2) (ZMod 3)) (fixed : binary ∈ binaryReducedRowStabilizer) :
    row ᵥ* (planeLevi binary 1).val = row := by
  obtain ⟨first, second⟩ := (binaryReducedRowStabilizer_mem binary).mp fixed
  ext column
  fin_cases column <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, planeLevi, planeBlock, zero, first, second]

theorem reduced_row_planeLevi_first (row : Fin 3 → ZMod 3)
    (binary : GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (row ᵥ* (planeLevi binary 1).val) 0 =
      (![row 0, row 1] ᵥ* binary.val) 0 := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, planeLevi, planeBlock]

theorem binaryRowLevel_levi_conjugate_mem (binary : binaryRowLevel)
    (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (zero : (lastRow ᵥ* (GeneralLinearGroup.map integralReduction matrix)⁻¹.val) 0 = 0) :
    (GeneralLinearGroup.map integralEmbedding matrix)⁻¹ * planeLevi binary.val 1 *
      GeneralLinearGroup.map integralEmbedding matrix ∈ finiteLevel := by
  obtain ⟨integralBinary, reduced, represents⟩ := binary.property
  refine ⟨matrix⁻¹ * planeLevi integralBinary 1 * matrix, ?_, ?_⟩
  · change lastRow ᵥ* (GeneralLinearGroup.map integralReduction
      (matrix⁻¹ * planeLevi integralBinary 1 * matrix)).val = lastRow
    simp only [map_mul, map_inv, map_planeLevi, map_one, Units.val_mul]
    rw [← vecMul_vecMul, ← vecMul_vecMul,
      reduced_row_planeLevi_fixed _ zero _ reduced, vecMul_vecMul,
      ← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one, vecMul_one]
  · simp only [map_mul, map_inv, map_planeLevi, map_one, represents]

theorem integral_plane_row_reduction (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    ∃ binary : SpecialLinearGroup (Fin 2) ℤ,
      (lastRow ᵥ* (GeneralLinearGroup.map integralReduction
        (planeLevi (SpecialLinearGroup.mapGL IntegralAdeles binary) 1 * matrix))⁻¹.val) 0 = 0 := by
  let row := lastRow ᵥ* (GeneralLinearGroup.map integralReduction matrix)⁻¹.val
  obtain ⟨binary, zero⟩ := binaryIntegralRowRepresentatives_reduce ![row 0, row 1]
  refine ⟨binary, ?_⟩
  have levi_inv : (planeLevi (SpecialLinearGroup.mapGL (ZMod 3) binary) 1)⁻¹ =
      planeLevi (SpecialLinearGroup.mapGL (ZMod 3) binary)⁻¹ 1 := by
    simpa [planeLeviHom] using
      (map_inv (planeLeviHom (ZMod 3)) (SpecialLinearGroup.mapGL (ZMod 3) binary, 1)).symm
  rw [map_mul, map_planeLevi, map_one, binaryIntegral_mapGL_map, _root_.mul_inv_rev, levi_inv]
  change (lastRow ᵥ* ((GeneralLinearGroup.map integralReduction matrix)⁻¹.val *
    (planeLevi (SpecialLinearGroup.mapGL (ZMod 3) binary)⁻¹ 1).val)) 0 = 0
  rw [← vecMul_vecMul, reduced_row_planeLevi_first]
  exact zero

theorem binaryIntegral_det_normPower (binary : GeneralLinearGroup (Fin 2) IntegralAdeles) (exponent : ℂ) :
    normPower (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding binary))) exponent = 1 := by
  have compact : inMaximalCompact (atFinite (planeLevi (GeneralLinearGroup.map integralEmbedding binary) 1)) := by
    constructor
    · rw [realGroup_atFinite]
      simp
    · rw [finiteGroup_atFinite]
      exact ⟨planeLevi binary 1, by rw [map_planeLevi, map_one]⟩
  have norm_one := normPower_det_compact _ compact exponent
  simpa only [atFinite_planeLevi, det_planeLevi, mul_one] using norm_one

theorem normalizedCuspVector_binaryRowLevel_fixed
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL)
    (integralMatrix : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (represents : GeneralLinearGroup.map integralEmbedding integralMatrix = finiteGroup matrix)
    (zero : (lastRow ᵥ* (GeneralLinearGroup.map integralReduction integralMatrix)⁻¹.val) 0 = 0)
    (binary : binaryRowLevel) :
    inducingData.cusp.π (atFinite binary.val) (normalizedCuspVector induced parameter matrix).val =
      (normalizedCuspVector induced parameter matrix).val := by
  have in_level : (finiteGroup matrix)⁻¹ * planeLevi binary.val 1 * finiteGroup matrix ∈ finiteLevel := by
    rw [← represents]
    exact binaryRowLevel_levi_conjugate_mem binary integralMatrix zero
  have norm_one : normPower (GeneralLinearGroup.det (atFinite binary.val)) (inductionExponent .plane parameter) = 1 := by
    obtain ⟨integralBinary, _, represents⟩ := binary.property
    rw [← represents]
    exact binaryIntegral_det_normPower integralBinary _
  have identity := normalizedCuspVector_binary induced parameter matrix (atFinite binary.val)
  rw [norm_one, one_smul, ← atFinite_planeLevi, atFinite_left_conjugate,
    normalizedCuspVector_finite_level induced parameter _ ⟨_, in_level⟩] at identity
  exact (congrArg Subtype.val identity).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
