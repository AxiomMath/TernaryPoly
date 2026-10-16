module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AdditiveIntegration

@[expose] public section


open MeasureTheory UnitAddTorus
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzPeriodization TernaryPeriodPolynomials.PlaneEisensteinContinuation.TorusPeriodization
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerCube
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerCube

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PeriodizationFourier

noncomputable def coordinateFunction (function : SchwartzMap RealSpace ℂ) : SchwartzMap (Coordinate → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℝ)).symm function

theorem coordinateFunction_apply (function : SchwartzMap RealSpace ℂ) (vector : Coordinate → ℝ) :
    coordinateFunction function vector = function (WithLp.toLp 2 vector) := rfl

noncomputable def character (frequency : Coordinate → ℤ) (vector : Coordinate → ℝ) : ℂ :=
  mFourier (-frequency) (toTorus (WithLp.toLp 2 vector))

theorem character_continuous (frequency : Coordinate → ℤ) : Continuous (character frequency) :=
  (mFourier (-frequency)).continuous.comp (toTorus_continuous.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℝ)).symm.continuous)

theorem character_norm_le (frequency : Coordinate → ℤ) (vector : Coordinate → ℝ) : ‖character frequency vector‖ ≤ 1 := by
  simpa only [character, mFourier_norm] using (mFourier (-frequency)).norm_coe_le_norm (toTorus (WithLp.toLp 2 vector))

theorem character_integer (frequency integer : Coordinate → ℤ) (vector : Coordinate → ℝ) :
    character frequency (integerCast integer + vector) = character frequency vector := by
  apply congrArg (mFourier (-frequency))
  apply (toTorus_eq_iff _ _).mpr
  refine ⟨integer, ?_⟩
  ext coordinate
  change (integer coordinate : ℝ) + vector coordinate = vector coordinate + (integer coordinate : ℝ)
  ring

noncomputable def weightedFunction (function : SchwartzMap RealSpace ℂ) (frequency : Coordinate → ℤ)
    (vector : Coordinate → ℝ) : ℂ := character frequency vector * coordinateFunction function vector

theorem weightedFunction_integrable (function : SchwartzMap RealSpace ℂ) (frequency : Coordinate → ℤ) :
    Integrable (weightedFunction function frequency) volume := by
  apply (coordinateFunction function).integrable.norm.mono'
    ((character_continuous frequency).mul (coordinateFunction function).continuous).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro vector
  change ‖character frequency vector * coordinateFunction function vector‖ ≤ ‖coordinateFunction function vector‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (character_norm_le frequency vector)

theorem coordinateFunction_shift (function : SchwartzMap RealSpace ℂ) (integer : Coordinate → ℤ) (vector : Coordinate → ℝ) :
    coordinateFunction function (integerCast integer + vector) = function (WithLp.toLp 2 vector + integerVector integer) := by
  apply congrArg function
  ext coordinate
  change (integer coordinate : ℝ) + vector coordinate = vector coordinate + (integer coordinate : ℝ)
  ring

theorem periodized_weighted (function : SchwartzMap RealSpace ℂ) (frequency : Coordinate → ℤ) (vector : Coordinate → ℝ) :
    (∑' integer : Coordinate → ℤ, weightedFunction function frequency (integerCast integer + vector)) =
      character frequency vector * periodization function (WithLp.toLp 2 vector) := by
  simp only [weightedFunction, character_integer, coordinateFunction_shift, tsum_mul_left]
  rfl

theorem coefficient_integral (function : SchwartzMap RealSpace ℂ) (frequency : Coordinate → ℤ) :
    mFourierCoeff (torusSum function) frequency = ∫ vector, weightedFunction function frequency vector := by
  rw [mFourierCoeff_eq_integral (torusSum function) frequency (0 : Coordinate → ℝ)]
  simp only [Pi.zero_apply, zero_add]
  change (∫ vector in cube, character frequency vector * torusSum function (toTorus (WithLp.toLp 2 vector))) = _
  simp only [torusSum_apply]
  calc
    (∫ vector in cube, character frequency vector * periodization function (WithLp.toLp 2 vector)) =
        ∫ vector in cube, ∑' integer : Coordinate → ℤ, weightedFunction function frequency (integerCast integer + vector) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun vector => (periodized_weighted function frequency vector).symm)
    _ = ∫ vector, weightedFunction function frequency vector :=
      AdditiveIntegration.integral_periodization cube_fundamental (weightedFunction_integrable function frequency)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PeriodizationFourier
