module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PrimitiveFrameRecovery

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PrimitiveFrameRecovery TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PrimitiveMass

theorem realCutoff_continuous (cutoff : Rectangular ℝ → ℝ) (continuous : Continuous cutoff) (point : AdelicGL) :
    Continuous (fun binary : BinaryAdelicGL => cutoff (coordinateEquiv.symm
      (archimedean (FrameProfile.frame point * binary.val)))) :=
  continuous.comp (coordinateEquiv.symm.toContinuousLinearEquiv.continuous.comp
    (AdelicSchwartzTheta.archimedean_continuous.comp
      (continuous_const.matrix_mul (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) Adeles)))))

theorem one_mem_integralRegion : (1 : BinaryAdelicGL) ∈ integralRegion := by
  refine ⟨1, ?_⟩
  simp only [map_one]

theorem nonzero_of_integrable (cutoff : Rectangular ℝ → ℝ) (continuous : Continuous cutoff)
    (nonnegative : ∀ value, 0 ≤ cutoff value) (point : AdelicGL)
    (positive : cutoff (realFrame point) ≠ 0)
    (integrable : IntegrableOn (fun binary : BinaryAdelicGL =>
      scalarCutoff cutoff (FrameProfile.frame point * binary.val)) integralRegion BinaryHaar.measure) :
    mass cutoff point ≠ 0 := by
  let function := fun binary : BinaryAdelicGL => cutoff (coordinateEquiv.symm
    (archimedean (FrameProfile.frame point * binary.val)))
  have continuousFunction : Continuous function := realCutoff_continuous cutoff continuous point
  have integrableFunction : IntegrableOn function integralRegion BinaryHaar.measure := by
    exact integrable.re
  have positiveMeasure : 0 < (BinaryHaar.measure.restrict integralRegion) (Function.support function) := by
    rw [Measure.restrict_apply' integralRegion_measurable]
    apply ((isOpen_ne_fun continuousFunction continuous_const).inter integralRegion_isOpen).measure_pos BinaryHaar.measure
    refine ⟨1, ?_, one_mem_integralRegion⟩
    change function 1 ≠ 0
    simpa only [function, Units.val_one, Matrix.mul_one, ← realFrame_eq] using positive
  have integralPositive : 0 < ∫ binary in integralRegion, function binary ∂BinaryHaar.measure :=
    (integral_pos_iff_support_of_nonneg (fun binary => nonnegative _) integrableFunction).mpr positiveMeasure
  have integralEquality : mass cutoff point = Complex.ofReal (∫ binary in integralRegion, function binary ∂BinaryHaar.measure) :=
    integral_ofReal (𝕜 := ℂ) (μ := BinaryHaar.measure.restrict integralRegion) (f := function)
  rw [integralEquality]
  exact_mod_cast integralPositive.ne'

theorem cutoff_integrable {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (test : Rectangular Adeles → data.cusp.smooth)
    (cutoff : Rectangular ℝ → ℝ)
    (interpolation : ∀ (finitePoint : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
      test (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value) =
        cutoff value • profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value))
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (nonzero : function point ≠ 0)
    (integrable : Integrable (VectorGodement.integrand data test parameter point) BinaryHaar.measure) :
    IntegrableOn (fun binary : BinaryAdelicGL => scalarCutoff cutoff (FrameProfile.frame point * binary.val))
      integralRegion BinaryHaar.measure := by
  have weighted : IntegrableOn (fun binary : BinaryAdelicGL =>
      scalarCutoff cutoff (FrameProfile.frame point * binary.val) *
        ((outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ * function point))
      integralRegion BinaryHaar.measure := by
    apply integrable.restrict.congr
    filter_upwards [ae_restrict_mem integralRegion_measurable] with binary membership
    exact PrimitiveFrameRecovery.integrand_eq induced test cutoff interpolation point pointIntegral binary membership
  exact (integrable_mul_const_iff (isUnit_iff_ne_zero.mpr
    (mul_ne_zero (inv_ne_zero (FrameProfile.character_ne_zero _ _)) nonzero)) _).mp weighted

theorem nonzero {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (test : Rectangular Adeles → data.cusp.smooth)
    (cutoff : Rectangular ℝ → ℝ) (continuous : Continuous cutoff) (nonnegative : ∀ value, 0 ≤ cutoff value)
    (interpolation : ∀ (finitePoint : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
      test (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value) =
        cutoff value • profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value))
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (sectionNonzero : function point ≠ 0) (cutoffNonzero : cutoff (realFrame point) ≠ 0)
    (integrable : Integrable (VectorGodement.integrand data test parameter point) BinaryHaar.measure) :
    mass cutoff point ≠ 0 :=
  nonzero_of_integrable cutoff continuous nonnegative point cutoffNonzero
    (cutoff_integrable induced test cutoff interpolation point pointIntegral sectionNonzero integrable)

theorem exists_cutoff {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction) (parameter : ℂ) (point : AdelicGL)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (sectionNonzero : sectionFunction parameter point ≠ 0) :
    ∃ cutoff : Rectangular ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff ∧ HasCompactSupport cutoff ∧
      tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value} ∧
      Set.range cutoff ⊆ Set.Icc 0 1 ∧ cutoff (realFrame point) = 1 ∧ mass cutoff point ≠ 0 := by
  obtain ⟨cutoff, smooth, compact, supported, range, value⟩ :=
    RealProfileCutoff.exists_cutoff (realFrame point) (realFrame_fullRank point)
  obtain ⟨test, _, _, integrable, interpolation⟩ :=
    FlatProfileInterpolation.exists_integrable_interpolation flat cutoff smooth compact supported
  refine ⟨cutoff, smooth, compact, supported, range, value, ?_⟩
  exact nonzero (flat.1 parameter) (test parameter) cutoff smooth.continuous
    (fun value => (range ⟨value, rfl⟩).1) (interpolation parameter) point pointIntegral
    sectionNonzero (by rw [value]; exact one_ne_zero) (integrable parameter point halfPlane)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PrimitiveMass
