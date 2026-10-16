module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RowAction
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowAction

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowActionContinuity

theorem continuous : Continuous (fun matrix : RealGL3 => (rowAction matrix).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro vector
  change Continuous (fun matrix : RealGL3 => WithLp.toLp 2 (vector.ofLp ᵥ* matrix.val))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_const.matrix_vecMul Units.continuous_val)

theorem inverse_continuous :
    Continuous (fun matrix : RealGL3 => (rowAction matrix).symm.toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro vector
  change Continuous (fun matrix : RealGL3 => WithLp.toLp 2 (vector.ofLp ᵥ* matrix.inv))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_const.matrix_vecMul Units.continuous_coe_inv)

theorem exists_distortion_bound (matrices : Set RealGL3) (compact : IsCompact matrices) :
    ∃ distortion : ℝ, 0 < distortion ∧ ∀ matrix ∈ matrices, ∀ vector : EuclideanSpace ℝ (Fin 3),
      ‖vector‖ ≤ distortion * ‖rowAction matrix vector‖ := by
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn inverse_continuous.continuousOn
  refine ⟨max bound 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun matrix membership vector => ?_⟩
  calc
    ‖vector‖ = ‖(rowAction matrix).symm (rowAction matrix vector)‖ := by
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ ≤ ‖(rowAction matrix).symm.toContinuousLinearMap‖ * ‖rowAction matrix vector‖ :=
      (rowAction matrix).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ max bound 1 * ‖rowAction matrix vector‖ :=
      mul_le_mul_of_nonneg_right ((bounded matrix membership).trans (le_max_left _ _)) (norm_nonneg _)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowActionContinuity
