module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Manifold

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem gammaOneThreeProduct_mdifferentiable {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gammaOneThreeProduct weight form) :=
  ((form.holo'.mul (gammaOneThree_slash_mdifferentiable form ModularGroup.S)).mul
    (gammaOneThree_slash_mdifferentiable form (ModularGroup.S * ModularGroup.T))).mul
      (gammaOneThree_slash_mdifferentiable form (ModularGroup.S * ModularGroup.T ^ 2))

theorem gammaOneThreeProduct_zero_at_infinity {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    UpperHalfPlane.IsZeroAtImInfty (gammaOneThreeProduct weight form) := by
  apply UpperHalfPlane.IsZeroAtImInfty.of_exp_decay
  refine ⟨4 * Real.pi, by positivity, ?_⟩
  simpa only [neg_mul] using gammaOneThreeProduct_exp_decay form

noncomputable def gammaOneThreeProductCuspForm {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (4 * weight) where
  toFun := gammaOneThreeProduct weight form
  slash_action_eq' matrix member := by
    obtain ⟨integralMatrix, rfl⟩ := member
    exact gammaOneThreeProduct_slash form integralMatrix
  holo' := gammaOneThreeProduct_mdifferentiable form
  zero_at_cusps' is_cusp := by
    apply (OnePoint.isZeroAt_iff_forall_SL2Z is_cusp).mpr
    intro matrix _
    change UpperHalfPlane.IsZeroAtImInfty
      (SlashAction.map (4 * weight) matrix (gammaOneThreeProduct weight form))
    rw [gammaOneThreeProduct_slash]
    exact gammaOneThreeProduct_zero_at_infinity form

theorem gammaOneThreeProduct_eq_zero_iff {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    gammaOneThreeProduct weight form = 0 ↔ form = 0 := by
  have first : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (form : UpperHalfPlane → ℂ) := form.holo'
  have second := gammaOneThree_slash_mdifferentiable form ModularGroup.S
  have third := gammaOneThree_slash_mdifferentiable form (ModularGroup.S * ModularGroup.T)
  have fourth := gammaOneThree_slash_mdifferentiable form (ModularGroup.S * ModularGroup.T ^ 2)
  rw [gammaOneThreeProduct, UpperHalfPlane.mul_eq_zero_iff ((first.mul second).mul third) fourth,
    UpperHalfPlane.mul_eq_zero_iff (first.mul second) third, UpperHalfPlane.mul_eq_zero_iff first second]
  simp only [SlashAction.slash_eq_zero_iff, or_self]
  exact FunLike.coe_zero_iff form

theorem full_cusp_eq_zero_of_small_weight_and_littleO {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (weight_small : weight < 24)
    (decay : (form : UpperHalfPlane → ℂ) =o[UpperHalfPlane.atImInfty] ModularForm.discriminant) :
    form = 0 := by
  have zero_at_infinity : UpperHalfPlane.IsZeroAtImInfty ((CuspForm.discriminantEquiv form) : UpperHalfPlane → ℂ) := by
    exact decay.tendsto_div_nhds_zero
  let quotient : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (weight - 12) :=
    { toFun := (CuspForm.discriminantEquiv form)
      slash_action_eq' := SlashInvariantFormClass.slash_action_eq (CuspForm.discriminantEquiv form)
      holo' := (CuspForm.discriminantEquiv form).holo'
      zero_at_cusps' := by
        intro cuspPoint is_cusp
        apply (OnePoint.isZeroAt_iff_forall_SL2Z is_cusp).mpr
        intro matrix _
        change UpperHalfPlane.IsZeroAtImInfty
          (SlashAction.map (weight - 12) (SpecialLinearGroup.mapGL ℝ matrix)
            ((CuspForm.discriminantEquiv form) : UpperHalfPlane → ℂ))
        rw [SlashInvariantFormClass.slash_action_eq
          (Γ := (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range)
          (CuspForm.discriminantEquiv form) (SpecialLinearGroup.mapGL ℝ matrix) ⟨matrix, rfl⟩]
        exact zero_at_infinity }
  obtain ⟨scalar, scalar_nonzero, scalar_zero⟩ :=
    rank_eq_zero_iff.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega : weight - 12 < 12)) quotient
  have quotient_zero : quotient = 0 := (smul_eq_zero.mp scalar_zero).resolve_left scalar_nonzero
  apply DFunLike.ext
  intro point
  have value := congrArg (fun f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
      (weight - 12) => f point) quotient_zero
  change form point / ModularForm.discriminant point = 0 at value
  exact (div_eq_zero_iff.mp value).resolve_right (ModularForm.discriminant_ne_zero point)

theorem gammaOneThreeProduct_littleO_discriminant {weight : ℤ} (form : CuspForm binaryRealGammaOneThree weight) :
    gammaOneThreeProduct weight form =o[UpperHalfPlane.atImInfty] ModularForm.discriminant := by
  have exp_decay : (fun point : UpperHalfPlane => Real.exp (-4 * Real.pi * point.im))
      =o[UpperHalfPlane.atImInfty] (fun point => Real.exp (-2 * Real.pi * point.im)) := by
    apply Real.isLittleO_exp_comp_exp_comp.mpr
    have height : Tendsto (fun point : UpperHalfPlane => point.im) UpperHalfPlane.atImInfty atTop := tendsto_comap
    have scaled := height.const_mul_atTop (by positivity : 0 < 2 * Real.pi)
    convert scaled using 1
    ext point
    ring
  exact ((gammaOneThreeProduct_exp_decay form).trans_isLittleO exp_decay).trans_isBigO
    ModularForm.exp_isBigO_discriminant

theorem gammaOneThree_cusp_eq_zero_of_weight_lt_six {weight : ℤ} (weight_small : weight < 6)
    (form : CuspForm binaryRealGammaOneThree weight) : form = 0 := by
  have product_zero := full_cusp_eq_zero_of_small_weight_and_littleO (gammaOneThreeProductCuspForm form)
    (by omega) (gammaOneThreeProduct_littleO_discriminant form)
  apply (gammaOneThreeProduct_eq_zero_iff form).mp
  exact congrArg (fun f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
    (4 * weight) => (f : UpperHalfPlane → ℂ)) product_zero

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
