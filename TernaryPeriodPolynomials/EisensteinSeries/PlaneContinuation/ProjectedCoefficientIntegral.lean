module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.CompactIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProjectedCoefficientIntegral

def joint (data : CuspidalRepresentation) (vector : data.smooth) (coefficient : BinaryFiniteGL → ℂ)
    (point : BinaryAdelicGL) (pair : BinaryFiniteGL × finiteCongruence) : ℂ :=
  coefficient pair.1 * data.realize vector (point * atFinite pair.2.val * atFinite pair.1)

theorem joint_integrable (data : CuspidalRepresentation) (vector : data.smooth)
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (point : BinaryAdelicGL) :
    Integrable (joint data vector coefficient point) (BinaryProductHaar.finiteMeasure.prod FiniteCompactIntegral.measure) := by
  have continuous : Continuous (fun pair : BinaryFiniteGL × finiteCongruence =>
      data.realize vector (point * atFinite pair.2.val * atFinite pair.1)) :=
    (CuspFunctionContinuity.continuous data vector).comp
      ((continuous_const.mul (atFinite_continuous.comp (continuous_subtype_val.comp continuous_snd))).mul
        (atFinite_continuous.comp continuous_fst))
  apply ((integrable.norm.mul_const (cuspSupNorm vector)).comp_fst FiniteCompactIntegral.measure).mono'
    ((integrable.comp_fst FiniteCompactIntegral.measure).aestronglyMeasurable.mul continuous.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro pair
  change ‖coefficient pair.1 * _‖ ≤ ‖coefficient pair.1‖ * cuspSupNorm vector
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (realize_le_cuspSupNorm vector _) (norm_nonneg _)

theorem realize_modeMap {degree : ℕ} (data : InducingData degree) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) (point : BinaryAdelicGL) :
    data.cusp.realize (modeMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
      coefficient integrable index vector).val point =
        ∫ element : finiteCongruence, (∫ binary : BinaryFiniteGL,
          coefficient binary * data.cusp.realize vector.val (point * atFinite element.val * atFinite binary)
            ∂BinaryProductHaar.finiteMeasure) ∂FiniteCompactIntegral.measure := by
  rw [FiniteModeConvolution.realize_modeMap]
  have equality (binary : BinaryFiniteGL) :
      coefficient binary * data.cusp.realize (FiniteModeConvolution.orbit data index vector binary).val point =
        ∫ element : finiteCongruence, joint data.cusp vector.val coefficient point (binary, element) ∂FiniteCompactIntegral.measure := by
    change coefficient binary * data.cusp.realize
      (AveragingSmooth.smoothAverage data.cusp finiteCongruence finiteCongruence_isCompact
        (FiniteModeConvolution.translated data.cusp vector.val binary)) point = _
    rw [FiniteCompactIntegral.realize_average, ← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro element
    dsimp only
    rw [FiniteModeConvolution.translated, data.cusp.equivariant]
    rfl
  simp_rw [equality]
  exact integral_integral_swap (joint_integrable data.cusp vector.val coefficient integrable point)

theorem recovery_realize {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (groupPoint : FiniteGL)
    (pointIntegral : groupPoint ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (modeMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
      (RecoveryCoefficients.coefficient data parameter (atFinite groupPoint) key)
      (RecoveryCoefficients.coefficient_integrable data parameter halfPlane (atFinite groupPoint) pointIntegral key)
      index vector).val evaluation =
        ∫ element : finiteCongruence,
          FiniteCoefficientEvaluation.integral data vector.val (UniversalFiniteProfiles.boxes data key)
            parameter groupPoint (evaluation * atFinite element.val) ∂FiniteCompactIntegral.measure :=
  realize_modeMap data index vector _ _ evaluation

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProjectedCoefficientIntegral
