module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Derivatives

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ClosedSubspaceAnalytic

variable {Domain Target : Type}
variable [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]

theorem derivative_mem (space : Submodule ℝ Target) (closed : IsClosed (space : Set Target))
    (function : Domain → space) (center : Domain)
    (analytic : AnalyticAt ℝ (fun point => (function point).val) center)
    (order : ℕ) (directions : Fin order → Domain) :
    iteratedFDeriv ℝ order (fun point => (function point).val) center directions ∈ space := by
  let _ : IsClosed (space : Set Target) := closed
  have zeroFunction : (space.mkQL ∘ fun point => (function point).val) = (0 : Domain → Target ⧸ space) := by
    funext point
    exact (Submodule.Quotient.mk_eq_zero space).mpr (function point).property
  have mapped := space.mkQL.iteratedFDeriv_comp_left (n := ⊤) analytic.contDiffAt (i := order) le_top
  rw [zeroFunction, iteratedFDeriv_zero] at mapped
  have zeroValue : space.mkQL (iteratedFDeriv ℝ order (fun point => (function point).val) center directions) = 0 := by
    exact (congrArg (fun coefficient => coefficient directions) mapped).symm
  exact (Submodule.Quotient.mk_eq_zero space).mp zeroValue

def taylor (space : Submodule ℝ Target) (closed : IsClosed (space : Set Target))
    (function : Domain → space) (center : Domain)
    (analytic : AnalyticAt ℝ (fun point => (function point).val) center) :
    FormalMultilinearSeries ℝ Domain space := fun order =>
  (((order.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ order (fun point => (function point).val) center).codRestrict
    space (fun directions => space.smul_mem _ (derivative_mem space closed function center analytic order directions))

theorem taylor_norm_le (space : Submodule ℝ Target) (closed : IsClosed (space : Set Target))
    (function : Domain → space) (center : Domain)
    (series : FormalMultilinearSeries ℝ Domain Target) (radius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (fun point => (function point).val) series center radius)
    (order : ℕ) :
    ‖taylor space closed function center expansion.hasFPowerSeriesAt.analyticAt order‖ ≤ ‖series order‖ := by
  have factorialPositive : (0 : ℝ) < order.factorial := by exact_mod_cast order.factorial_pos
  have derivativeBound := AnalyticDerivatives.powerSeries_iteratedFDeriv_norm_le expansion order
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro directions
  change ‖(order.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ order (fun point => (function point).val) center directions‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr factorialPositive.le)]
  calc
    _ ≤ (order.factorial : ℝ)⁻¹ *
        (‖iteratedFDeriv ℝ order (fun point => (function point).val) center‖ * ∏ index, ‖directions index‖) :=
      mul_le_mul_of_nonneg_left ((iteratedFDeriv ℝ order (fun point => (function point).val) center).le_opNorm _)
        (inv_nonneg.mpr factorialPositive.le)
    _ ≤ (order.factorial : ℝ)⁻¹ * ((order.factorial : ℝ) * ‖series order‖ * ∏ index, ‖directions index‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right derivativeBound (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
        (inv_nonneg.mpr factorialPositive.le)
    _ = _ := by field_simp

theorem taylor_apply_diag (space : Submodule ℝ Target) (closed : IsClosed (space : Set Target))
    (function : Domain → space) (center : Domain)
    (series : FormalMultilinearSeries ℝ Domain Target) (radius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (fun point => (function point).val) series center radius)
    (order : ℕ) (offset : Domain) :
    (taylor space closed function center expansion.hasFPowerSeriesAt.analyticAt order (fun _ => offset)).val =
      series order (fun _ => offset) := by
  change (order.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ order (fun point => (function point).val) center (fun _ => offset) = _
  rw [← expansion.factorial_smul offset order, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast order.factorial_ne_zero), one_smul]

theorem hasFPowerSeries (space : Submodule ℝ Target) (closed : IsClosed (space : Set Target))
    (function : Domain → space) (center : Domain)
    (series : FormalMultilinearSeries ℝ Domain Target) (radius : ENNReal)
    (expansion : HasFPowerSeriesOnBall (fun point => (function point).val) series center radius) :
    HasFPowerSeriesOnBall function (taylor space closed function center expansion.hasFPowerSeriesAt.analyticAt)
      center radius := by
  refine ⟨expansion.r_le.trans (FormalMultilinearSeries.radius_le_of_le
    (taylor_norm_le space closed function center series radius expansion)), expansion.r_pos, ?_⟩
  intro offset membership
  have summed := expansion.hasSum membership
  change Filter.Tendsto (fun indices : Finset ℕ => ∑ order ∈ indices,
    taylor space closed function center expansion.hasFPowerSeriesAt.analyticAt order (fun _ => offset))
    Filter.atTop (nhds (function (center + offset)))
  apply tendsto_subtype_rng.mpr
  simp only [Submodule.coe_sum, taylor_apply_diag space closed function center series radius expansion]
  exact summed

theorem analyticAt (space : Submodule ℝ Target) (closed : IsClosed (space : Set Target))
    (function : Domain → space) (center : Domain)
    (analytic : AnalyticAt ℝ (fun point => (function point).val) center) :
    AnalyticAt ℝ function center := by
  obtain ⟨series, radius, expansion⟩ := analytic
  exact (hasFPowerSeries space closed function center series radius expansion).hasFPowerSeriesAt.analyticAt

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ClosedSubspaceAnalytic
