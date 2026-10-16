module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.Coefficients
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RecoveryAsymptotic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FinitePrimitiveRecovery TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteMatrixWeight TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoverySupport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryCoefficients TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryOperatorLimit

theorem shifted_halfPlane {degree : ℕ} (reference : ℂ) (halfPlane : -(degree : ℝ) / 2 ≤ reference.re)
    (index : ℕ) : -(degree : ℝ) / 2 ≤ (reference + index).re := by
  simp only [Complex.add_re, Complex.natCast_re]
  exact halfPlane.trans (le_add_of_nonneg_right (Nat.cast_nonneg index))

theorem coefficient_shift {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : AdelicGL)
    (key : UniversalFiniteProfiles.Key data) (index : ℕ) (binary : BinaryFiniteGL) :
    coefficient data (reference + index) point key binary =
      (weight binary : ℂ) ^ index * coefficient data reference point key binary := by
  have difference : reference + (index : ℂ) - reference = (index : ℂ) := by ring
  rw [coefficient, FlatFrameProfile.inner_change_parameter data (reference + index) reference,
    difference, FiniteRecoveryAsymptotic.normPower_nat, coefficient]
  unfold weight
  ring

def primitiveCoefficient {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : AdelicGL)
    (key : UniversalFiniteProfiles.Key data) : BinaryFiniteGL → ℂ :=
  integralGroup.indicator (coefficient data reference point key)

theorem primitive_integrable {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) :
    Integrable (primitiveCoefficient data reference point key) BinaryProductHaar.finiteMeasure :=
  (coefficient_integrable data reference halfPlane point pointIntegral key).indicator integralGroup_isOpen.measurableSet

theorem complex_weight_norm (binary : BinaryFiniteGL) : ‖(weight binary : ℂ)‖ = weight binary := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos binary)]

theorem weight_primitive (binary : BinaryFiniteGL) (primitive : binary ∈ integralGroup) : weight binary = 1 := by
  obtain ⟨integer, rfl⟩ := primitive
  exact weight_integral integer

theorem difference_bound {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) (index : ℕ) (binary : BinaryFiniteGL) :
    ‖coefficient data (reference + index) point key binary - primitiveCoefficient data reference point key binary‖ ≤
      ‖coefficient data reference point key binary‖ := by
  rw [coefficient_shift, primitiveCoefficient]
  by_cases primitive : binary ∈ integralGroup
  · rw [Set.indicator_of_mem primitive, weight_primitive binary primitive, Complex.ofReal_one,
      one_pow, one_mul, sub_self, norm_zero]
    exact norm_nonneg _
  · rw [Set.indicator_of_notMem primitive, sub_zero]
    by_cases integral : IntegralMatrix binary
    · rw [norm_mul, norm_pow, complex_weight_norm]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_one₀ (weight_pos binary).le (norm_le_one binary integral)) (norm_nonneg _)).trans_eq (one_mul _)
    · rw [coefficient_supported data reference point pointIntegral key binary integral, mul_zero]

theorem coefficient_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) (binary : BinaryFiniteGL) :
    Tendsto (fun index : ℕ => coefficient data (reference + index) point key binary) atTop
      (nhds (primitiveCoefficient data reference point key binary)) := by
  simp only [coefficient_shift, primitiveCoefficient]
  by_cases primitive : binary ∈ integralGroup
  · simp only [Set.indicator_of_mem primitive, weight_primitive binary primitive, Complex.ofReal_one, one_pow, one_mul]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem primitive]
    by_cases integral : IntegralMatrix binary
    · have small : ‖(weight binary : ℂ)‖ < 1 := by
        rw [complex_weight_norm]
        exact norm_lt_one binary integral primitive
      simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one small).mul_const
        (coefficient data reference point key binary)
    · simp only [coefficient_supported data reference point pointIntegral key binary integral, mul_zero]
      exact tendsto_const_nhds

theorem difference_integral_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) :
    Tendsto (fun index : ℕ => ∫ binary,
      ‖coefficient data (reference + index) point key binary - primitiveCoefficient data reference point key binary‖
        ∂BinaryProductHaar.finiteMeasure) atTop (nhds 0) := by
  have result := tendsto_integral_of_dominated_convergence
    (fun binary => ‖coefficient data reference point key binary‖)
    (fun index => ((coefficient_integrable data (reference + index) (shifted_halfPlane reference halfPlane index)
      point pointIntegral key).sub (primitive_integrable data reference halfPlane point pointIntegral key)).norm.aestronglyMeasurable)
    (coefficient_integrable data reference halfPlane point pointIntegral key).norm
    (fun index => Eventually.of_forall (fun binary => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact difference_bound data reference point pointIntegral key index binary))
    (Eventually.of_forall (fun binary => by
      simpa only [Pi.sub_apply, sub_self, norm_zero] using
        ((coefficient_tendsto data reference point pointIntegral key binary).sub_const
          (primitiveCoefficient data reference point key binary)).norm))
  simpa only [Pi.sub_apply, integral_zero] using result

def primitiveOperator {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) : data.cusp.H →L[ℂ] data.cusp.H :=
  FiniteHilbertConvolution.operator data.cusp (primitiveCoefficient data reference point key)
    (primitive_integrable data reference halfPlane point pointIntegral key)

theorem operator_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) :
    Tendsto (fun index : ℕ => RecoveryCoefficients.operator data (reference + index)
      (shifted_halfPlane reference halfPlane index) point pointIntegral key) atTop
      (nhds (primitiveOperator data reference halfPlane point pointIntegral key)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun index => operator_difference_bound data.cusp
      (coefficient data (reference + index) point key) (primitiveCoefficient data reference point key)
      (coefficient_integrable data (reference + index) (shifted_halfPlane reference halfPlane index) point pointIntegral key)
      (primitive_integrable data reference halfPlane point pointIntegral key)))
    (difference_integral_tendsto data reference halfPlane point pointIntegral key)

theorem projected_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) :
    Tendsto (fun index : ℕ => RecoveryCoefficients.projected data (reference + index)
      (shifted_halfPlane reference halfPlane index) point pointIntegral key) atTop
      (nhds ((CompactAveraging.averagingOperator data.cusp BinaryLevel.finiteCongruence).comp
        (primitiveOperator data reference halfPlane point pointIntegral key))) :=
  (((ContinuousLinearMap.compL ℂ data.cusp.H data.cusp.H data.cusp.H)
    (CompactAveraging.averagingOperator data.cusp BinaryLevel.finiteCongruence)).continuous.tendsto _).comp
      (operator_tendsto data reference halfPlane point pointIntegral key)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryOperatorLimit
