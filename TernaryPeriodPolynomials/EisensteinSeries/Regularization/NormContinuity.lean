module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.Continuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem finiteIntegralUnits_isOpen :
    IsOpen (Set.range (Units.map integralEmbedding.toMonoidHom)) := by
  simpa only [Set.image_univ] using
    (Units.isOpenMap_map integralEmbedding_injective integralEmbedding_isOpenEmbedding.isOpenMap)
      Set.univ isOpen_univ

theorem adeleUnit_eq_real_integral (idele : Adelesˣ) (integralUnit : IntegralAdelesˣ)
    (finite_integral : Units.map integralEmbedding.toMonoidHom integralUnit =
      Units.map (RingHom.snd ℝ FiniteAdeles).toMonoidHom idele) :
    idele = realAdeleUnit (Units.map (RingHom.fst ℝ FiniteAdeles).toMonoidHom idele) *
      integralAdeleUnit integralUnit := by
  apply Units.ext
  apply Prod.ext
  · change idele.val.1 = idele.val.1 * 1
    exact (mul_one _).symm
  · change idele.val.2 = 1 * integralEmbedding integralUnit.val
    rw [one_mul]
    exact (congrArg Units.val finite_integral).symm

theorem adeleNorm_of_finite_integral (idele : Adelesˣ)
    (finite_integral : Units.map (RingHom.snd ℝ FiniteAdeles).toMonoidHom idele ∈
      Set.range (Units.map integralEmbedding.toMonoidHom)) :
    (adeleNorm idele : ℝ) = |idele.val.1| := by
  obtain ⟨integralUnit, integral_spec⟩ := finite_integral
  calc
    _ = (adeleNorm
        (realAdeleUnit (Units.map (RingHom.fst ℝ FiniteAdeles).toMonoidHom idele) *
          integralAdeleUnit integralUnit) : ℝ) :=
      congrArg (fun unit => (adeleNorm unit : ℝ)) (adeleUnit_eq_real_integral idele integralUnit integral_spec)
    _ = _ := by
      rw [map_mul, NNReal.coe_mul, adeleNorm_integralAdeleUnit, NNReal.coe_one, mul_one,
        adeleNorm_realAdeleUnit]
      rfl

theorem adeleNorm_continuous : Continuous adeleNorm := by
  apply continuous_of_continuousAt_one adeleNorm
  have model_continuous : Continuous (fun idele : Adelesˣ =>
      (⟨|idele.val.1|, abs_nonneg _⟩ : NNReal)) :=
    ((continuous_fst.comp Units.continuous_val).abs).subtype_mk _
  apply model_continuous.continuousAt.congr_of_eventuallyEq
  have near : ∀ᶠ idele : Adelesˣ in nhds 1,
      Units.map (RingHom.snd ℝ FiniteAdeles).toMonoidHom idele ∈
        Set.range (Units.map integralEmbedding.toMonoidHom) :=
    (finiteIntegralUnits_isOpen.preimage (Units.continuous_map continuous_snd)).eventually_mem
      ⟨1, by simp⟩
  filter_upwards [near] with idele finite_integral
  exact Subtype.ext (adeleNorm_of_finite_integral idele finite_integral)

theorem normPower_continuous : Continuous (fun input : Adelesˣ × ℂ => normPower input.1 input.2) := by
  have positive : ∀ input : Adelesˣ × ℂ, (adeleNorm input.1 : ℝ) ≠ 0 :=
    fun input => ne_of_gt (NNReal.coe_pos.mpr (adeleNorm_pos input.1))
  have log_continuous := (NNReal.continuous_coe.comp (adeleNorm_continuous.comp continuous_fst)).log positive
  exact (continuous_snd.mul (Complex.continuous_ofReal.comp log_continuous)).cexp

theorem adelicDet_continuous : Continuous (GeneralLinearGroup.det : AdelicGL → Adelesˣ) := by
  have determinant_continuous : Continuous (Matrix.det : Matrix (Fin 3) (Fin 3) Adeles → Adeles) :=
    continuous_id.matrix_det
  exact Units.continuous_iff.mpr ⟨determinant_continuous.comp Units.continuous_val,
    determinant_continuous.comp (Units.continuous_val.comp continuous_inv)⟩

theorem unitaryNormalize_continuous
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) : Continuous (unitaryNormalize degree family parameter) :=
  (normPower_continuous.comp (adelicDet_continuous.prodMk continuous_const)).mul
    (induced_continuous (induced (parameter - ((degree : ℂ) + 3) / 2)))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
