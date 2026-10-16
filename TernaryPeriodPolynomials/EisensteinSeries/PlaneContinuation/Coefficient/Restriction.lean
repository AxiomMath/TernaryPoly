module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.TranslatedSeries

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientRestriction

theorem norm_restrict_le {Source Domain Target : Type}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (linear : Domain →L[ℝ] Source) (linearBound : ‖linear‖ ≤ 1) (order : ℕ)
    (coefficient : ContinuousMultilinearMap ℝ (fun _ : Fin order => Source) Target) :
    ‖coefficient.compContinuousLinearMap (fun _ => linear)‖ ≤ ‖coefficient‖ := by
  apply (coefficient.norm_compContinuousLinearMap_le (fun _ => linear)).trans
  have productBound : (∏ _ : Fin order, ‖linear‖) ≤ 1 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (ContinuousLinearMap.opNorm_nonneg linear) linearBound
  exact mul_le_of_le_one_right (norm_nonneg _) productBound

noncomputable def restrictLinear {Source Domain Target : Type}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (linear : Domain →L[ℝ] Source) (linearBound : ‖linear‖ ≤ 1) :
    lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => Source) Target) ⊤ →ₗ[ℝ]
      lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) Target) ⊤ where
  toFun coefficients := ⟨fun order => (coefficients order).compContinuousLinearMap (fun _ => linear),
    memℓp_infty (by
      refine ⟨‖coefficients‖, ?_⟩
      rintro value ⟨order, rfl⟩
      exact (norm_restrict_le linear linearBound order (coefficients order)).trans
        (lp.norm_apply_le_norm (by simp) coefficients order))⟩
  map_add' first second := by
    apply Subtype.ext
    funext order
    apply ContinuousMultilinearMap.ext
    intro directions
    rfl
  map_smul' scalar coefficients := by
    apply Subtype.ext
    funext order
    apply ContinuousMultilinearMap.ext
    intro directions
    rfl

theorem norm_restrictLinear_le {Source Domain Target : Type}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (linear : Domain →L[ℝ] Source) (linearBound : ‖linear‖ ≤ 1)
    (coefficients : lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => Source) Target) ⊤) :
    ‖restrictLinear linear linearBound coefficients‖ ≤ ‖coefficients‖ := by
  apply lp.norm_le_of_forall_le'
  intro order
  exact (norm_restrict_le linear linearBound order (coefficients order)).trans
    (lp.norm_apply_le_norm (by simp) coefficients order)

noncomputable def restrictCoefficients {Source Domain Target : Type}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (linear : Domain →L[ℝ] Source) (linearBound : ‖linear‖ ≤ 1) :
    lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => Source) Target) ⊤ →L[ℝ]
      lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) Target) ⊤ :=
  (restrictLinear linear linearBound).mkContinuous 1 (fun coefficients => by
    simpa only [one_mul] using norm_restrictLinear_le linear linearBound coefficients)

theorem restrictCoefficients_apply {Source Domain Target : Type}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (linear : Domain →L[ℝ] Source) (linearBound : ‖linear‖ ≤ 1)
    (coefficients : lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => Source) Target) ⊤)
    (order : ℕ) :
    restrictCoefficients linear linearBound coefficients order =
      (coefficients order).compContinuousLinearMap (fun _ => linear) := rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientRestriction
