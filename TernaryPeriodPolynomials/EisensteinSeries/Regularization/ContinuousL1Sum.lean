module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ContinuousMapPowerSeries
public import Mathlib.Analysis.Normed.Lp.lpSpace

@[expose] public section


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

variable {X F : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [TopologicalSpace X] [CompactSpace X] in
theorem l1Complex_norm_summable (coefficients : lp (fun _ : X => ℂ) 1) :
    Summable (fun point => ‖coefficients point‖) := by
  have summable := (memℓp_gen_iff (p := 1) (by norm_num)).mp coefficients.property
  simpa only [ENNReal.toReal_one, Real.rpow_one] using summable

omit [TopologicalSpace X] [CompactSpace X] in
theorem l1Complex_norm_eq_tsum (coefficients : lp (fun _ : X => ℂ) 1) :
    ‖coefficients‖ = ∑' point, ‖coefficients point‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, div_one] using
    lp.norm_eq_tsum_rpow (p := 1) (by norm_num) coefficients

omit [CompleteSpace F] in
theorem continuousL1Sum_norm_summable (function : C(X, F)) (coefficients : lp (fun _ : X => ℂ) 1) :
    Summable (fun point => ‖coefficients point • function point‖) := by
  apply ((l1Complex_norm_summable coefficients).mul_right ‖function‖).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro point
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (function.norm_coe_le_norm point) (norm_nonneg _)

theorem continuousL1Sum_summable (function : C(X, F)) (coefficients : lp (fun _ : X => ℂ) 1) :
    Summable (fun point => coefficients point • function point) :=
  (continuousL1Sum_norm_summable function coefficients).of_norm

omit [CompleteSpace F] in
theorem continuousL1Sum_bound (function : C(X, F)) (coefficients : lp (fun _ : X => ℂ) 1) :
    ‖∑' point, coefficients point • function point‖ ≤ ‖function‖ * ‖coefficients‖ := by
  calc
    _ ≤ ∑' point, ‖coefficients point • function point‖ := norm_tsum_le_tsum_norm
      (continuousL1Sum_norm_summable function coefficients)
    _ ≤ ∑' point, ‖coefficients point‖ * ‖function‖ :=
      Summable.tsum_le_tsum
        (f := fun point : X => ‖coefficients point • function point‖)
        (g := fun point : X => ‖coefficients point‖ * ‖function‖)
        (fun point => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (function.norm_coe_le_norm point) (norm_nonneg _))
        (continuousL1Sum_norm_summable function coefficients)
        ((l1Complex_norm_summable coefficients).mul_right ‖function‖)
    _ = _ := by rw [tsum_mul_right, ← l1Complex_norm_eq_tsum, mul_comm]

noncomputable def continuousL1SumLinear (function : C(X, F)) :
    lp (fun _ : X => ℂ) 1 →ₗ[ℂ] F where
  toFun coefficients := ∑' point, coefficients point • function point
  map_add' first second := by
    change (∑' point, (first point + second point) • function point) = _
    simp only [add_smul]
    exact (continuousL1Sum_summable function first).tsum_add (continuousL1Sum_summable function second)
  map_smul' scalar coefficients := by
    change (∑' point, (scalar * coefficients point) • function point) = _
    simp only [mul_smul]
    exact Summable.tsum_const_smul scalar (continuousL1Sum_summable function coefficients)

noncomputable def continuousL1Sum (function : C(X, F)) : lp (fun _ : X => ℂ) 1 →L[ℂ] F :=
  (continuousL1SumLinear function).mkContinuous ‖function‖ (continuousL1Sum_bound function)

theorem continuousL1Sum_apply (function : C(X, F)) (coefficients : lp (fun _ : X => ℂ) 1) :
    continuousL1Sum function coefficients = ∑' point, coefficients point • function point := rfl

noncomputable def continuousL1SumFunctionLinear (coefficients : lp (fun _ : X => ℂ) 1) : C(X, F) →ₗ[ℂ] F where
  toFun function := continuousL1Sum function coefficients
  map_add' first second := by
    change (∑' point, coefficients point • (first point + second point)) = _
    simp only [smul_add]
    exact (continuousL1Sum_summable first coefficients).tsum_add (continuousL1Sum_summable second coefficients)
  map_smul' scalar function := by
    change (∑' point, coefficients point • (scalar • function point)) = _
    simp only [smul_comm (coefficients _) scalar]
    exact Summable.tsum_const_smul scalar (continuousL1Sum_summable function coefficients)

noncomputable def continuousL1SumFunction (coefficients : lp (fun _ : X => ℂ) 1) : C(X, F) →L[ℂ] F :=
  (continuousL1SumFunctionLinear coefficients).mkContinuous ‖coefficients‖ (by
    intro function
    change ‖∑' point, coefficients point • function point‖ ≤ ‖coefficients‖ * ‖function‖
    rw [mul_comm]
    exact continuousL1Sum_bound function coefficients)

theorem continuousL1Sum_single [DecidableEq X] (function : C(X, F)) (point : X) (scalar : ℂ) :
    continuousL1Sum function (lp.single 1 point scalar) = scalar • function point := by
  classical
  rw [continuousL1Sum_apply]
  rw [tsum_eq_single point]
  · simp
  · intro other distinct
    rw [lp.single_apply_ne _ _ _ distinct, zero_smul]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
