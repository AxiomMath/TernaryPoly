module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RecoverySupport

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealBinaryRecovery
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FinitePrimitiveRecovery TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryMellin
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryAsymptotic

def weight (binary : BinaryFiniteGL) : ℂ := (adeleNorm (GeneralLinearGroup.det (atFinite binary)) : ℝ)

theorem weight_norm (binary : BinaryFiniteGL) :
    ‖weight binary‖ = (adeleNorm (GeneralLinearGroup.det (atFinite binary)) : ℝ) := by
  rw [weight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]

theorem normPower_nat (scalar : Adelesˣ) (index : ℕ) :
    normPower scalar (index : ℂ) = ((adeleNorm scalar : ℝ) : ℂ) ^ index := by
  rw [normPower, Complex.exp_nat_mul, ← Complex.ofReal_exp]
  have equality : Real.exp (Real.log (adeleNorm scalar : ℝ)) = (adeleNorm scalar : ℝ) :=
    Real.exp_log (adeleNorm_pos scalar)
  exact congrArg (fun value : ℝ => (value : ℂ) ^ index) equality

theorem norm_bound {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : BinaryFiniteGL) (index : ℕ) :
    ‖weight binary ^ index * kernel induced point (atFinite binary)‖ ≤ ‖kernel induced point (atFinite binary)‖ := by
  by_cases nonzero : kernel induced point (atFinite binary) = 0
  · rw [nonzero, mul_zero, norm_zero]
  · have frameIntegral : finite (FrameProfile.frame point * (atFinite binary).val) ∈ Set.range CompactFiniteFrames.embedding := by
      by_contra outside
      exact nonzero (kernel_supported induced point (atFinite binary) outside)
    have bound : ‖weight binary‖ ≤ 1 := by
      rw [weight_norm]
      exact FiniteRecoverySupport.norm_le_one binary
        (FiniteRecoverySupport.integralMatrix_of_frame point pointIntegral binary frameIntegral)
    rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) bound) (norm_nonneg _)).trans_eq (one_mul _)

theorem pointwise_limit {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : BinaryFiniteGL) :
    Tendsto (fun index : ℕ => weight binary ^ index * kernel induced point (atFinite binary)) atTop
      (nhds (integralGroup.indicator (fun binary => kernel induced point (atFinite binary)) binary)) := by
  by_cases primitive : binary ∈ integralGroup
  · obtain ⟨integer, equality⟩ := primitive
    have weightOne : weight binary = 1 := by
      rw [weight, ← equality, Norm.adeleNorm_det_integral]
      rfl
    simpa only [weightOne, one_pow, one_mul, Set.indicator_of_mem (show binary ∈ integralGroup from ⟨integer, equality⟩)]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => kernel induced point (atFinite binary)) atTop _)
  · rw [Set.indicator_of_notMem primitive]
    by_cases nonzero : kernel induced point (atFinite binary) = 0
    · simp only [nonzero, mul_zero]
      exact tendsto_const_nhds
    · have frameIntegral : finite (FrameProfile.frame point * (atFinite binary).val) ∈ Set.range CompactFiniteFrames.embedding := by
        by_contra outside
        exact nonzero (kernel_supported induced point (atFinite binary) outside)
      have bound : ‖weight binary‖ < 1 := by
        rw [weight_norm]
        exact FiniteRecoverySupport.norm_lt_one binary
          (FiniteRecoverySupport.integralMatrix_of_frame point pointIntegral binary frameIntegral) primitive
      simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one bound).mul_const
        (kernel induced point (atFinite binary))

theorem weighted_kernel_eq {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (reference : ℂ) (point : AdelicGL)
    (compact : inMaximalCompact point) (index : ℕ) (binary : BinaryFiniteGL) :
    weight binary ^ index * kernel (flat.1 reference) point (atFinite binary) =
      kernel (flat.1 (reference + index)) point (atFinite binary) := by
  have difference : reference + (index : ℂ) - reference = (index : ℂ) := by ring
  have equality := kernel_parameter flat (reference + index) reference point binary
  simpa only [difference, realFactor, realHeight_orthogonal point compact.1, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_mul, normPower_nat, weight] using equality.symm

theorem weighted_integral_tendsto {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (reference : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < reference.re)
    (point : AdelicGL) (compact : inMaximalCompact point) :
    Tendsto (fun index : ℕ => ∫ binary : BinaryFiniteGL,
      weight binary ^ index * kernel (flat.1 reference) point (atFinite binary) ∂BinaryProductHaar.finiteMeasure) atTop
      (nhds (∫ binary in integralGroup,
        kernel (flat.1 reference) point (atFinite binary) ∂BinaryProductHaar.finiteMeasure)) := by
  have integrable (index : ℕ) : Integrable (fun binary : BinaryFiniteGL =>
      weight binary ^ index * kernel (flat.1 reference) point (atFinite binary)) BinaryProductHaar.finiteMeasure := by
    simp only [weighted_kernel_eq flat reference point compact index]
    apply kernel_integrable flat (reference + index) point
    simp only [Complex.add_re, Complex.natCast_re]
    exact lt_of_lt_of_le halfPlane (le_add_of_nonneg_right (Nat.cast_nonneg index))
  have result := tendsto_integral_of_dominated_convergence
    (fun binary : BinaryFiniteGL => ‖kernel (flat.1 reference) point (atFinite binary)‖)
    (fun index => (integrable index).aestronglyMeasurable) (kernel_integrable flat reference point halfPlane).norm
    (fun index => Eventually.of_forall (fun binary => norm_bound (flat.1 reference) point compact.2 binary index))
    (Eventually.of_forall (pointwise_limit (flat.1 reference) point compact.2))
  simpa only [integral_indicator integralGroup_isOpen.measurableSet] using result

theorem section_tendsto {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (reference : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < reference.re)
    (point : AdelicGL) (compact : inMaximalCompact point) :
    Tendsto (fun index : ℕ => FiniteRecoveryIntegral.sectionFunction (flat.1 (reference + index)) point) atTop
      (nhds ((mass : ℂ) * function reference point)) := by
  have result := (weighted_integral_tendsto flat reference halfPlane point compact).const_mul
    (GodementIntegral.outerCharacter data reference (GeneralLinearGroup.det point))
  have functionEquality (index : ℕ) : FiniteRecoveryIntegral.sectionFunction (flat.1 (reference + index)) point =
      GodementIntegral.outerCharacter data reference (GeneralLinearGroup.det point) *
        ∫ binary : BinaryFiniteGL, weight binary ^ index * kernel (flat.1 reference) point (atFinite binary)
          ∂BinaryProductHaar.finiteMeasure := by
    rw [section_parameter_compact flat (reference + index) reference point compact]
    have difference : reference + (index : ℂ) - reference = (index : ℂ) := by ring
    simp only [difference, normPower_nat, weight]
  have limitEquality : GodementIntegral.outerCharacter data reference (GeneralLinearGroup.det point) *
      (∫ binary in integralGroup, kernel (flat.1 reference) point (atFinite binary) ∂BinaryProductHaar.finiteMeasure) =
        (mass : ℂ) * function reference point := by
    rw [primitive_integral (flat.1 reference) point compact.2]
    have nonzero := FrameProfile.character_ne_zero (GodementIntegral.outerCharacter data reference)
      (GeneralLinearGroup.det point)
    field_simp
  simpa only [functionEquality, limitEquality] using result

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryAsymptotic
