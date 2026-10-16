module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.ScalarDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalar TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarSeries

theorem smoothMode_iteratedDerivative (data : CuspidalRepresentation) (vector : data.smooth)
    (index : ℤ) (order : ℕ) :
    smoothMode data index ((rotationDerivative data ^ order) vector) =
      frequency index ^ order • smoothMode data index vector :=
  Subtype.ext (modeVector_iteratedDerivative data vector index order)

theorem cuspSupNorm_mode_frequency_bound (data : CuspidalRepresentation) (vector : data.smooth)
    (index : ℤ) (order : ℕ) :
    ‖frequency index‖ ^ order * cuspSupNorm (smoothMode data index vector) ≤
      cuspSupNorm ((rotationDerivative data ^ order) vector) := by
  have estimate := cuspSupNorm_smoothMode_le data index ((rotationDerivative data ^ order) vector)
  rw [smoothMode_iteratedDerivative, cuspSupNorm_smul, norm_pow] at estimate
  exact estimate

theorem cuspSupNorm_mode_bound (data : CuspidalRepresentation) (vector : data.smooth)
    (index : ℤ) (nonzeroIndex : index ≠ 0) :
    cuspSupNorm (smoothMode data index vector) ≤
      (cuspSupNorm ((rotationDerivative data ^ 2) vector) / (2 * Real.pi) ^ 2) *
        (1 / (index : ℝ) ^ 2) := by
  have frequencyNorm : ‖frequency index‖ = (2 * Real.pi) * |(index : ℝ)| := by
    simpa only [frequency, Int.cast_zero, mul_zero, sub_zero] using frequency_sub_norm index 0
  have estimate := cuspSupNorm_mode_frequency_bound data vector index 2
  rw [frequencyNorm, mul_pow, sq_abs] at estimate
  have nonzeroCast : (index : ℝ) ≠ 0 := by exact_mod_cast nonzeroIndex
  have positiveDenominator : (0 : ℝ) < (2 * Real.pi) ^ 2 * (index : ℝ) ^ 2 :=
    mul_pos (sq_pos_of_pos (by positivity)) (sq_pos_of_ne_zero nonzeroCast)
  have equality :
      (cuspSupNorm ((rotationDerivative data ^ 2) vector) / (2 * Real.pi) ^ 2) *
          (1 / (index : ℝ) ^ 2) =
        cuspSupNorm ((rotationDerivative data ^ 2) vector) / ((2 * Real.pi) ^ 2 * (index : ℝ) ^ 2) := by
    ring
  rw [equality, le_div_iff₀ positiveDenominator]
  simpa only [mul_comm] using estimate

theorem summable_cuspSupNorm_modes (data : CuspidalRepresentation) (vector : data.smooth) :
    Summable (fun index : ℤ => cuspSupNorm (smoothMode data index vector)) := by
  have series : Summable (fun index : ℤ => (1 : ℝ) / (index : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have majorant := (series.mul_left
    (cuspSupNorm ((rotationDerivative data ^ 2) vector) / (2 * Real.pi) ^ 2)).add
      (hasSum_ite_eq (0 : ℤ) (cuspSupNorm vector)).summable
  apply majorant.of_nonneg_of_le (fun _ => cuspSupNorm_nonneg _)
  intro index
  by_cases zeroIndex : index = 0
  · subst index
    simpa using cuspSupNorm_smoothMode_le data 0 vector
  · simpa only [ite_eq_right zeroIndex, add_zero] using cuspSupNorm_mode_bound data vector index zeroIndex

theorem summable_realized_modes (data : CuspidalRepresentation) (vector : data.smooth) :
    Summable (fun index : ℤ => boundedRealization data (smoothMode data index vector)) :=
  (summable_cuspSupNorm_modes data vector).of_norm

theorem scalar_modes_hasSum (data : CuspidalRepresentation) (vector : data.smooth)
    (point : BinaryAdelicGL) :
    HasSum (fun index : ℤ => data.realize (smoothMode data index vector) point) (data.realize vector point) := by
  have summability : Summable (fun index : ℤ => fourierCoeff (scalarOrbit data point vector) index) := by
    apply (summable_cuspSupNorm_modes data vector).of_norm_bounded
    intro index
    change ‖scalarCoefficient data point index vector‖ ≤ _
    rw [scalarCoefficient_eq_mode]
    exact realize_le_cuspSupNorm _ _
  have expansion := ContinuousMap.hasSum_apply (hasSum_fourier_series_of_summable summability) (0 : Parameter)
  have coefficients (index : ℤ) : fourierCoeff (scalarOrbit data point vector) index =
      data.realize (smoothMode data index vector) point := scalarCoefficient_eq_mode data point index vector
  simp only [ContinuousMap.smul_apply, fourier_eval_zero, smul_eq_mul, mul_one] at expansion
  simp_rw [coefficients] at expansion
  simpa only [scalarOrbit, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk,
    rotation_zero, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, mul_one] using expansion

/-- Fourier projections reconstruct the realization in the full supremum norm over the adelic group. -/
theorem realized_modes_hasSum (data : CuspidalRepresentation) (vector : data.smooth) :
    HasSum (fun index : ℤ => boundedRealization data (smoothMode data index vector))
      (boundedRealization data vector) := by
  have summability := summable_realized_modes data vector
  have equality : (∑' index : ℤ, boundedRealization data (smoothMode data index vector)) =
      boundedRealization data vector := by
    apply Subtype.ext
    funext point
    have pointwise := (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ point).hasSum summability.hasSum
    exact (scalar_modes_hasSum data vector point).unique pointwise |>.symm
  exact equality ▸ summability.hasSum

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarSeries
