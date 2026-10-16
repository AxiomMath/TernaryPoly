module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Stages

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BoundedFamilies

theorem hasSum_single_of_summable_norm {Index : Type} {Values : Index → Type}
    [DecidableEq Index]
    [∀ index, NormedAddCommGroup (Values index)] [∀ index, NormedSpace ℝ (Values index)]
    [∀ index, CompleteSpace (Values index)]
    (function : lp Values ⊤) (summableNorm : Summable (fun index => ‖function index‖)) :
    HasSum (fun index => lp.single ⊤ index (function index)) function := by
  classical
  have summable : Summable (fun index => lp.single ⊤ index (function index)) :=
    summableNorm.of_norm_bounded (fun index => (lp.norm_single (by simp) index (function index)).le)
  have equality : (∑' index, lp.single ⊤ index (function index)) = function := by
    apply Subtype.ext
    funext index
    have mappedSum := (lp.evalCLM ℝ Values ⊤ index).hasSum summable.hasSum
    have coordinateSum : HasSum (fun other => (lp.single ⊤ other (function other)) index) (function index) := by
      have isolated := hasSum_single (f := fun other => (lp.single ⊤ other (function other)) index) index
        (fun other inequality => lp.single_apply_ne ⊤ other (function other) inequality.symm)
      exact (congrArg (fun total : Values index =>
        HasSum (fun other => (lp.single ⊤ other (function other)) index) total)
          (lp.single_apply_self ⊤ index (function index))).mp isolated
    exact mappedSum.unique coordinateSum
  exact (congrArg (fun total : lp Values ⊤ => HasSum (fun index => lp.single ⊤ index (function index)) total)
    equality).mp summable.hasSum

theorem continuousOn_of_summable_bound {Index Parameter : Type} {Values : Index → Type}
    [TopologicalSpace Parameter]
    [∀ index, NormedAddCommGroup (Values index)] [∀ index, NormedSpace ℝ (Values index)]
    [∀ index, CompleteSpace (Values index)]
    (family : Parameter → lp Values ⊤) {domain : Set Parameter}
    (coordinateContinuous : ∀ index, ContinuousOn (fun parameter => family parameter index) domain)
    {bound : Index → ℝ} (summableBound : Summable bound)
    (estimate : ∀ parameter ∈ domain, ∀ index, ‖family parameter index‖ ≤ bound index) :
    ContinuousOn family domain := by
  classical
  have summandsContinuous (index : Index) :
      ContinuousOn (fun parameter => lp.single ⊤ index (family parameter index)) domain :=
    (lp.singleContinuousLinearMap ℝ Values ⊤ index).continuous.comp_continuousOn (coordinateContinuous index)
  have summandsBound (index : Index) (parameter : Parameter) (membership : parameter ∈ domain) :
      ‖lp.single ⊤ index (family parameter index)‖ ≤ bound index :=
    (lp.norm_single (by simp) index (family parameter index)).trans_le (estimate parameter membership index)
  have sumContinuous := continuousOn_tsum summandsContinuous summableBound summandsBound
  apply sumContinuous.congr
  intro parameter membership
  have summableNorm : Summable (fun index => ‖family parameter index‖) :=
    summableBound.of_nonneg_of_le (fun _ => norm_nonneg _) (estimate parameter membership)
  exact (hasSum_single_of_summable_norm (family parameter) summableNorm).tsum_eq.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BoundedFamilies
