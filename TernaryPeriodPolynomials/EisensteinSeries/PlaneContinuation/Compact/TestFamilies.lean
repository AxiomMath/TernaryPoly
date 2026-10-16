module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.BanachLift

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactTestFamilies

variable {Parameter Domain Target : Type}
variable [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
variable [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem partial_derivative (function : Parameter × Domain → Target)
    (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) function) (parameter : Parameter) (point : Domain) (order : ℕ) :
    iteratedFDeriv ℝ order (fun value => function (parameter, value)) point =
      (iteratedFDeriv ℝ order function (parameter, point)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ Parameter Domain) := by
  let shifted : Parameter × Domain → Target := fun value => function (value + (parameter, 0))
  have shiftedSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) shifted := smooth.comp (contDiff_id.add contDiff_const)
  have equality := (ContinuousLinearMap.inr ℝ Parameter Domain).iteratedFDeriv_comp_right shiftedSmooth point
    (i := order) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  simpa only [shifted, Function.comp_def, ContinuousLinearMap.inr_apply, iteratedFDeriv_comp_add_right,
    Prod.mk_add_mk, zero_add, add_zero] using equality

theorem partial_derivative_norm_le (function : Parameter × Domain → Target)
    (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) function) (parameter : Parameter) (point : Domain) (order : ℕ) :
    ‖iteratedFDeriv ℝ order (fun value => function (parameter, value)) point‖ ≤
      ‖iteratedFDeriv ℝ order function (parameter, point)‖ := by
  rw [partial_derivative function smooth parameter point order]
  apply ((iteratedFDeriv ℝ order function (parameter, point)).norm_compContinuousLinearMap_le _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ Parameter Domain)

theorem derivative_zero_outside (function : Domain → Target) (compactSet : Set Domain)
    (closed : IsClosed compactSet) (vanishing : ∀ point ∉ compactSet, function point = 0)
    (point : Domain) (outside : point ∉ compactSet) (order : ℕ) :
    iteratedFDeriv ℝ order function point = 0 := by
  have equality : function =ᶠ[nhds point] 0 := by
    filter_upwards [closed.isOpen_compl.mem_nhds outside] with value membership
    exact vanishing value membership
  simpa only [iteratedFDeriv_zero, Pi.zero_apply] using (equality.iteratedFDeriv ℝ order).eq_of_nhds

theorem uniform_derivative_bound (function : Parameter × Domain → Target)
    (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) function)
    (spatialSet : Set Domain) (spatialCompact : IsCompact spatialSet)
    (vanishing : ∀ parameter point, point ∉ spatialSet → function (parameter, point) = 0)
    (parameterSet : Set Parameter) (parameterCompact : IsCompact parameterSet) (weight order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameterSet, ∀ point,
      ‖point‖ ^ weight * ‖iteratedFDeriv ℝ order (fun value => function (parameter, value)) point‖ ≤ bound := by
  have derivativeContinuous : Continuous (fun pair : Parameter × Domain =>
      ‖pair.2‖ ^ weight * ‖iteratedFDeriv ℝ order function pair‖) :=
    (continuous_snd.norm.pow weight).mul ((smooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm)
  obtain ⟨bound, boundProperty⟩ := (parameterCompact.prod spatialCompact).exists_bound_of_continuousOn derivativeContinuous.continuousOn
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro parameter parameterMembership point
  by_cases inside : point ∈ spatialSet
  · calc
      _ ≤ ‖point‖ ^ weight * ‖iteratedFDeriv ℝ order function (parameter, point)‖ :=
        mul_le_mul_of_nonneg_left (partial_derivative_norm_le function smooth parameter point order)
          (pow_nonneg (norm_nonneg _) weight)
      _ ≤ ‖‖point‖ ^ weight * ‖iteratedFDeriv ℝ order function (parameter, point)‖‖ := le_abs_self _
      _ ≤ bound := boundProperty (parameter, point) ⟨parameterMembership, inside⟩
      _ ≤ _ := le_max_right _ _
  · rw [derivative_zero_outside _ spatialSet spatialCompact.isClosed (vanishing parameter) point inside order, norm_zero, mul_zero]
    exact le_max_left _ _

variable [NormedSpace ℂ Target] [IsScalarTower ℝ ℂ Target]

theorem uniform_seminorm_bound (tests : Parameter → SchwartzMap Domain Target)
    (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun pair : Parameter × Domain => tests pair.1 pair.2))
    (spatialSet : Set Domain) (spatialCompact : IsCompact spatialSet)
    (vanishing : ∀ parameter point, point ∉ spatialSet → tests parameter point = 0)
    (parameterSet : Set Parameter) (parameterCompact : IsCompact parameterSet) (weight order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameterSet,
      SchwartzMap.seminorm ℂ weight order (tests parameter) ≤ bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := uniform_derivative_bound
    (fun pair : Parameter × Domain => tests pair.1 pair.2) smooth spatialSet spatialCompact vanishing
    parameterSet parameterCompact weight order
  exact ⟨bound, nonnegative, fun parameter membership =>
    SchwartzMap.seminorm_le_bound ℂ weight order (tests parameter) nonnegative (bounded parameter membership)⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactTestFamilies
