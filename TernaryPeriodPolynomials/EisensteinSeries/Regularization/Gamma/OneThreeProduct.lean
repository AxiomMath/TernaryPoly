module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeBasic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem gammaOneThree_form_slash_neg {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (member : -matrix ∈ CongruenceSubgroup.Gamma1 3) :
    SlashAction.map weight matrix (form : UpperHalfPlane → ℂ) = ((-1 : ℂ) ^ (-weight)) • form := by
  have identity : matrix = (-1) * (-matrix) := by simp
  conv_lhs => rw [identity]
  rw [SlashAction.slash_mul, scalar_slash_neg_one, ModularForm.SL_smul_slash,
    gammaOneThree_form_slash form _ member]

theorem gammaOneThree_form_slash_correction {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight)
    (first second : SpecialLinearGroup (Fin 2) ℤ)
    (member : first * second⁻¹ ∈ CongruenceSubgroup.Gamma1 3) :
    SlashAction.map weight first (form : UpperHalfPlane → ℂ) = SlashAction.map weight second (form : UpperHalfPlane → ℂ) := by
  have identity := SlashAction.slash_mul weight (first * second⁻¹) second (form : UpperHalfPlane → ℂ)
  rw [mul_assoc, inv_mul_cancel, mul_one, gammaOneThree_form_slash form _ member] at identity
  exact identity

theorem gammaOneThree_form_slash_neg_correction {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight)
    (first second : SpecialLinearGroup (Fin 2) ℤ)
    (member : -(first * second⁻¹) ∈ CongruenceSubgroup.Gamma1 3) :
    SlashAction.map weight first (form : UpperHalfPlane → ℂ) =
      ((-1 : ℂ) ^ (-weight)) • SlashAction.map weight second (form : UpperHalfPlane → ℂ) := by
  have identity := SlashAction.slash_mul weight (first * second⁻¹) second (form : UpperHalfPlane → ℂ)
  rw [mul_assoc, inv_mul_cancel, mul_one, gammaOneThree_form_slash_neg form _ member,
    ModularForm.SL_smul_slash] at identity
  exact identity

theorem scalar_slash_four (weight : ℤ) (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (first second third fourth : UpperHalfPlane → ℂ) :
    SlashAction.map (4 * weight) matrix (first * second * third * fourth) =
      SlashAction.map weight matrix first * SlashAction.map weight matrix second *
        SlashAction.map weight matrix third * SlashAction.map weight matrix fourth := by
  rw [show 4 * weight = (weight + weight) + weight + weight by ring,
    ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2]

noncomputable def gammaOneThreeProduct (weight : ℤ) (function : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  function * SlashAction.map weight ModularGroup.S function *
    SlashAction.map weight (ModularGroup.S * ModularGroup.T) function *
      SlashAction.map weight (ModularGroup.S * ModularGroup.T ^ 2) function

theorem gammaOneThreeProduct_T {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    SlashAction.map (4 * weight) ModularGroup.T (gammaOneThreeProduct weight form) =
      gammaOneThreeProduct weight form := by
  have last : SlashAction.map weight ((ModularGroup.S * ModularGroup.T ^ 2) * ModularGroup.T)
      (form : UpperHalfPlane → ℂ) = SlashAction.map weight ModularGroup.S (form : UpperHalfPlane → ℂ) := by
    apply gammaOneThree_form_slash_correction
    simpa only [pow_succ, mul_assoc] using gammaOneThree_ST3S_mem
  rw [gammaOneThreeProduct, scalar_slash_four, gammaOneThree_form_slash form _ gammaOneThree_T_mem]
  simp only [← SlashAction.slash_mul]
  rw [last]
  have middle : (ModularGroup.S * ModularGroup.T) * ModularGroup.T =
      ModularGroup.S * ModularGroup.T ^ 2 := by simp only [pow_two, mul_assoc]
  rw [middle]
  ring

theorem gammaOneThreeProduct_S {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    SlashAction.map (4 * weight) ModularGroup.S (gammaOneThreeProduct weight form) =
      gammaOneThreeProduct weight form := by
  have third := gammaOneThree_form_slash_correction form
    (ModularGroup.S * ModularGroup.T * ModularGroup.S) (ModularGroup.S * ModularGroup.T ^ 2)
    gammaOneThree_STS_correction_mem
  have fourth := gammaOneThree_form_slash_neg_correction form
    (ModularGroup.S * ModularGroup.T ^ 2 * ModularGroup.S) (ModularGroup.S * ModularGroup.T)
    gammaOneThree_ST2S_correction_mem
  rw [gammaOneThreeProduct, scalar_slash_four]
  simp only [← SlashAction.slash_mul]
  rw [modularGroup_S_sq, scalar_slash_neg_one, third, fourth]
  funext point
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, neg_one_zpow_eq_ite]
  split_ifs <;> ring

theorem gammaOneThreeProduct_slash {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map (4 * weight) matrix (gammaOneThreeProduct weight form) = gammaOneThreeProduct weight form :=
  SlashInvariantForm.slash_action_generators_SL2Z (gammaOneThreeProduct_S form) (gammaOneThreeProduct_T form) matrix

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
