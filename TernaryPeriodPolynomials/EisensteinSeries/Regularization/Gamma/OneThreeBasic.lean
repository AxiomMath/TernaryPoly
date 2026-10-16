module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.IntegralModularLevel
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryRealGammaOneThree : Subgroup BinaryRealGL :=
  (CongruenceSubgroup.Gamma1 3).map (SpecialLinearGroup.mapGL ℝ)

instance binaryRealGammaOneThree_hasDetOne : binaryRealGammaOneThree.HasDetOne where
  det_eq := by
    rintro matrix ⟨integralMatrix, _, rfl⟩
    exact SpecialLinearGroup.det_mapGL integralMatrix

instance binaryRealGammaOneThree_isArithmetic : binaryRealGammaOneThree.IsArithmetic :=
  Subgroup.isArithmetic_iff_finiteIndex.mpr inferInstance

theorem gammaOneThree_form_slash {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (member : matrix ∈ CongruenceSubgroup.Gamma1 3) :
    SlashAction.map weight matrix (form : UpperHalfPlane → ℂ) = form := by
  exact SlashInvariantFormClass.slash_action_eq form (SpecialLinearGroup.mapGL ℝ matrix)
    ⟨matrix, member, rfl⟩

theorem scalar_slash_neg_one (weight : ℤ) (function : UpperHalfPlane → ℂ) :
    SlashAction.map weight (-1 : SpecialLinearGroup (Fin 2) ℤ) function =
      ((-1 : ℂ) ^ (-weight)) • function := by
  funext point
  simp [ModularForm.SL_slash_def, UpperHalfPlane.denom, mul_comm]

theorem gammaOneThree_T_mem : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 3 := by
  rw [CongruenceSubgroup.Gamma1_mem]
  norm_num [ModularGroup.T]

theorem gammaOneThree_ST3S_mem :
    ModularGroup.S * ModularGroup.T ^ 3 * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma1 3 := by
  rw [CongruenceSubgroup.Gamma1_mem]
  decide

theorem gammaOneThree_STS_correction_mem :
    ModularGroup.S * ModularGroup.T * ModularGroup.S * (ModularGroup.S * ModularGroup.T ^ 2)⁻¹ ∈
      CongruenceSubgroup.Gamma1 3 := by
  rw [CongruenceSubgroup.Gamma1_mem]
  decide

theorem gammaOneThree_ST2S_correction_mem :
    -(ModularGroup.S * ModularGroup.T ^ 2 * ModularGroup.S * (ModularGroup.S * ModularGroup.T)⁻¹) ∈
      CongruenceSubgroup.Gamma1 3 := by
  rw [CongruenceSubgroup.Gamma1_mem]
  decide

theorem modularGroup_S_sq : ModularGroup.S * ModularGroup.S = -1 := by
  decide

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
