module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeProduct
public import Mathlib.NumberTheory.ModularForms.QExpansion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Manifold

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem scalar_periodic_of_slash_T_zpow (weight period : ℤ) (function : UpperHalfPlane → ℂ)
    (invariant : SlashAction.map weight (ModularGroup.T ^ period) function = function) :
    Function.Periodic (function ∘ UpperHalfPlane.ofComplex) (period : ℂ) := by
  have translation (point : UpperHalfPlane) : function ((period : ℝ) +ᵥ point) = function point := by
    have value := congrFun invariant point
    have action : ModularGroup.T ^ period • point = (period : ℝ) +ᵥ point := by
      apply UpperHalfPlane.ext
      rw [ModularGroup.coe_T_zpow_smul_eq]
      simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast, add_comm]
    have denominator : UpperHalfPlane.denom
        (SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ period)) point = 1 := by
      change ((SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ period)).val 1 0 : ℂ) * (point : ℂ) +
        ((SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ period)).val 1 1 : ℂ) = 1
      rw [binaryIntegral_mapGL_entry, binaryIntegral_mapGL_entry]
      norm_num [ModularGroup.coe_T_zpow]
    have mapped : SpecialLinearGroup.toGL
        (SpecialLinearGroup.map (Int.castRingHom ℝ) (ModularGroup.T ^ period)) =
        SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ period) := by
      apply Units.ext
      apply Matrix.ext
      intro row column
      change (((ModularGroup.T ^ period).val row column : ℤ) : ℝ) = _
      rw [binaryIntegral_mapGL_entry]
    rw [ModularForm.SL_slash_apply, mapped, denominator, _root_.one_zpow, mul_one, action] at value
    exact value
  intro point
  change function (UpperHalfPlane.ofComplex (point + (period : ℂ))) = function (UpperHalfPlane.ofComplex point)
  by_cases positive : 0 < point.im
  · have shifted : UpperHalfPlane.ofComplex (point + (period : ℂ)) =
        (period : ℝ) +ᵥ UpperHalfPlane.ofComplex point := by
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.ofComplex_apply_eq_ite, positive, add_comm]
    rw [shifted]
    exact translation _
  · have shifted_nonpositive : ¬ 0 < (point + (period : ℂ)).im := by simpa using positive
    simp only [UpperHalfPlane.ofComplex_apply_eq_ite, dite_eq_right positive, dite_eq_right shifted_nonpositive]

theorem gammaOneThree_slash_mdifferentiable {weight : ℤ}
    (form : CuspForm binaryRealGammaOneThree weight) (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (SlashAction.map weight matrix (form : UpperHalfPlane → ℂ)) := by
  rw [ModularForm.SL_slash]
  exact form.holo'.slash weight _

theorem gammaOneThree_periodic {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    Function.Periodic ((form : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (1 : ℂ) := by
  have invariant : SlashAction.map weight (ModularGroup.T ^ (1 : ℤ)) (form : UpperHalfPlane → ℂ) = form := by
    simpa only [zpow_one] using gammaOneThree_form_slash form ModularGroup.T gammaOneThree_T_mem
  simpa only [Int.cast_one] using scalar_periodic_of_slash_T_zpow weight 1 form invariant

theorem gammaOneThree_ST_periodic {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) (power : ℕ) :
    Function.Periodic
      (SlashAction.map weight (ModularGroup.S * ModularGroup.T ^ power) (form : UpperHalfPlane → ℂ) ∘
        UpperHalfPlane.ofComplex) (3 : ℂ) := by
  apply scalar_periodic_of_slash_T_zpow weight 3
  rw [← SlashAction.slash_mul]
  apply gammaOneThree_form_slash_correction
  have correction : (ModularGroup.S * ModularGroup.T ^ power * ModularGroup.T ^ (3 : ℤ)) *
      (ModularGroup.S * ModularGroup.T ^ power)⁻¹ = ModularGroup.S * ModularGroup.T ^ 3 * ModularGroup.S⁻¹ := by
    rw [zpow_ofNat, _root_.mul_inv_rev]
    have commute : ModularGroup.T ^ power * ModularGroup.T ^ 3 =
        ModularGroup.T ^ 3 * ModularGroup.T ^ power := by rw [← pow_add, ← pow_add, Nat.add_comm]
    calc
      _ = ModularGroup.S * (ModularGroup.T ^ power * ModularGroup.T ^ 3) *
          (ModularGroup.T ^ power)⁻¹ * ModularGroup.S⁻¹ := by simp only [mul_assoc]
      _ = _ := by rw [commute]; simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [correction]
  exact gammaOneThree_ST3S_mem

theorem gammaOneThree_exp_decay {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    (form : UpperHalfPlane → ℂ) =O[UpperHalfPlane.atImInfty]
      (fun point => Real.exp (-2 * Real.pi * point.im)) := by
  have zero_at_infinity : UpperHalfPlane.IsZeroAtImInfty (form : UpperHalfPlane → ℂ) := by
    simpa using CuspFormClass.zero_at_infty_slash form (1 : SpecialLinearGroup (Fin 2) ℤ)
  simpa only [div_one] using zero_at_infinity.exp_decay_atImInfty (by norm_num : (0 : ℝ) < 1)
    (gammaOneThree_periodic form) form.holo' zero_at_infinity.isBoundedAtImInfty

theorem gammaOneThree_ST_exp_decay {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) (power : ℕ) :
    SlashAction.map weight (ModularGroup.S * ModularGroup.T ^ power) (form : UpperHalfPlane → ℂ)
      =O[UpperHalfPlane.atImInfty] (fun point => Real.exp (-2 * Real.pi * point.im / 3)) := by
  have zero_at_infinity := CuspFormClass.zero_at_infty_slash form (ModularGroup.S * ModularGroup.T ^ power)
  exact zero_at_infinity.exp_decay_atImInfty (by norm_num : (0 : ℝ) < 3)
    (gammaOneThree_ST_periodic form power) (gammaOneThree_slash_mdifferentiable form _)
    zero_at_infinity.isBoundedAtImInfty

theorem gammaOneThreeProduct_exp_decay {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    gammaOneThreeProduct weight form =O[UpperHalfPlane.atImInfty]
      (fun point => Real.exp (-4 * Real.pi * point.im)) := by
  have first := gammaOneThree_exp_decay form
  have second := gammaOneThree_ST_exp_decay form 0
  have third := gammaOneThree_ST_exp_decay form 1
  have fourth := gammaOneThree_ST_exp_decay form 2
  have product := ((first.mul second).mul third).mul fourth
  simpa only [gammaOneThreeProduct, Pi.mul_def, pow_zero, mul_one, pow_one, ← Real.exp_add,
    show ∀ height : ℝ, -2 * Real.pi * height + -2 * Real.pi * height / 3 +
      -2 * Real.pi * height / 3 + -2 * Real.pi * height / 3 = -4 * Real.pi * height from
      fun height => by ring] using product

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
