module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.TaylorBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RadicalIntegralBound

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open MeasureTheory
open scoped NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TaylorIntegral

/-- Integrable Taylor coefficients with a geometric bound on their integral
norms may be integrated term by term on the common ball of convergence. -/
theorem hasFPowerSeriesOnBall {A E F : Type} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (measure : Measure A) (family : A → E → F) (series : A → FormalMultilinearSeries ℝ E F)
    (center : E) (radius : ℝ≥0) (positive : 0 < radius) (constant : ℝ)
    (expansion : ∀ argument, HasFPowerSeriesOnBall (family argument) (series argument) center radius)
    (integrable : ∀ order, Integrable (fun argument => series argument order) measure)
    (bounded : ∀ order, (∫ argument, ‖series argument order‖ ∂measure) ≤
      constant * (radius : ℝ)⁻¹ ^ order) :
    HasFPowerSeriesOnBall (fun point => ∫ argument, family argument point ∂measure)
      (fun order => ∫ argument, series argument order ∂measure) center radius := by
  have integratedBound (order : ℕ) : ‖∫ argument, series argument order ∂measure‖ ≤
      constant * (radius : ℝ)⁻¹ ^ order :=
    (norm_integral_le_integral_norm _).trans (bounded order)
  refine ⟨CompactTaylorBounds.radius_of_coefficient_bound _ radius positive constant integratedBound,
    by exact_mod_cast positive, ?_⟩
  intro offset membership
  have offsetLess : ‖offset‖ < (radius : ℝ) := by
    simpa only [Metric.eball_coe, Metric.mem_ball, dist_zero_right] using membership
  have radiusPositive : (0 : ℝ) < radius := by exact_mod_cast positive
  have ratioNonnegative : 0 ≤ ‖offset‖ / (radius : ℝ) := div_nonneg (norm_nonneg _) radius.property
  have ratioLess : ‖offset‖ / (radius : ℝ) < 1 := (div_lt_one radiusPositive).mpr offsetLess
  have evalIntegrable (order : ℕ) :
      Integrable (fun argument => series argument order (fun _ => offset)) measure :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => E) F (fun _ => offset)).integrable_comp
      (integrable order)
  have evalBound (order : ℕ) :
      (∫ argument, ‖series argument order (fun _ => offset)‖ ∂measure) ≤
        constant * (‖offset‖ / (radius : ℝ)) ^ order := by
    calc
      _ ≤ ∫ argument, ‖series argument order‖ * ‖offset‖ ^ order ∂measure :=
        integral_mono (evalIntegrable order).norm ((integrable order).norm.mul_const _)
          (fun argument => by simpa using (series argument order).le_opNorm (fun _ => offset))
      _ = (∫ argument, ‖series argument order‖ ∂measure) * ‖offset‖ ^ order := integral_mul_const _ _
      _ ≤ (constant * (radius : ℝ)⁻¹ ^ order) * ‖offset‖ ^ order :=
        mul_le_mul_of_nonneg_right (bounded order) (pow_nonneg (norm_nonneg _) _)
      _ = constant * (‖offset‖ / (radius : ℝ)) ^ order := by
        rw [div_eq_mul_inv, mul_pow]
        ring
  have summable : Summable (fun order =>
      ∫ argument, ‖series argument order (fun _ => offset)‖ ∂measure) :=
    ((summable_geometric_of_lt_one ratioNonnegative ratioLess).mul_left constant).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) evalBound
  have sums := hasSum_integral_of_summable_integral_norm evalIntegrable summable
  have seriesEquality : (fun order => (∫ argument, series argument order ∂measure) (fun _ => offset)) =
      (fun order => ∫ argument, series argument order (fun _ => offset) ∂measure) := by
    funext order
    exact ContinuousMultilinearMap.integral_apply (integrable order) _
  rw [seriesEquality]
  convert sums using 1
  apply integral_congr_ae
  filter_upwards [] with argument
  exact ((expansion argument).hasSum membership).tsum_eq.symm

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TaylorIntegral
