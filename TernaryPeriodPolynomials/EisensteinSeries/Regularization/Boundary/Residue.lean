module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.PoleOrder

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def normalizedBoundaryResidue (degree : ℕ) (continuation : ℂ → AdelicGL → ℂ)
    (matrix : AdelicGL) : ℂ :=
  toMeromorphicNFAt (fun parameter => (parameter - (3 : ℂ) / 2) *
    unitaryNormalize degree continuation parameter matrix) ((3 : ℂ) / 2) ((3 : ℂ) / 2)

theorem normalized_boundary_product_meromorphic
    {degree : ℕ} {family continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation family continuation) (matrix : AdelicGL) :
    MeromorphicAt (fun parameter => (parameter - (3 : ℂ) / 2) *
      unitaryNormalize degree continuation parameter matrix) ((3 : ℂ) / 2) :=
  (analyticAt_id.sub analyticAt_const).meromorphicAt.mul
    ((unitaryNormalize_continuation degree continuation_spec).1 matrix _)

theorem normalizedBoundaryResidue_tendsto
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (matrix : AdelicGL) :
    Tendsto (fun displacement : ℝ => (displacement : ℂ) *
      ∑' flag, eisensteinSummand (unitaryNormalize degree family)
        ((3 : ℂ) / 2 + (displacement : ℂ)) matrix flag)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (normalizedBoundaryResidue degree continuation matrix)) := by
  have meromorphic := normalized_boundary_product_meromorphic (degree := degree) continuation_spec matrix
  have analytic := meromorphic.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
    (normalized_continuation_boundary_product_order flat continuation_spec matrix)
  have limit := analytic.continuousAt.tendsto.comp
    ((positive_real_ray_tendsto ((3 : ℂ) / 2)).mono_right nhdsWithin_le_nhds)
  apply limit.congr'
  filter_upwards [normalized_continuation_boundary_ray_eq_actual_sum flat continuation_spec matrix,
    self_mem_nhdsWithin] with displacement same positive
  change 0 < displacement at positive
  have point_ne : (3 : ℂ) / 2 + (displacement : ℂ) ≠ (3 : ℂ) / 2 := by
    intro equality
    exact (ne_of_gt positive) (Complex.ofReal_eq_zero.mp (add_eq_left.mp equality))
  dsimp only [Function.comp_def]
  rw [← meromorphic.eqOn_compl_singleton_toMeromorphicNFAt point_ne]
  simp only [add_sub_cancel_left, same]

theorem normalizedBoundaryResidue_compact_bound
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (matrices : Set AdelicGL) (compact : IsCompact matrices) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ matrix ∈ matrices, ‖normalizedBoundaryResidue degree continuation matrix‖ ≤ bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalized_scalar_sum_compact_boundary_bound flat matrices compact
  refine ⟨bound, nonnegative, ?_⟩
  intro matrix member
  apply le_of_tendsto (normalizedBoundaryResidue_tendsto flat continuation_spec matrix).norm
  filter_upwards [bounded, self_mem_nhdsWithin] with displacement bounded positive
  change 0 < displacement at positive
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  exact bounded matrix member

theorem normalizedBoundaryResidue_eq_zero_iff_order_nonnegative
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (matrix : AdelicGL) :
    normalizedBoundaryResidue degree continuation matrix = 0 ↔
      0 ≤ meromorphicOrderAt (fun parameter => unitaryNormalize degree continuation parameter matrix) ((3 : ℂ) / 2) := by
  have meromorphic := normalized_boundary_product_meromorphic (degree := degree) continuation_spec matrix
  have equivalence := meromorphic.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero
  change _ ↔ normalizedBoundaryResidue degree continuation matrix ≠ 0 at equivalence
  have product_order := fun_meromorphicOrderAt_mul
    (f := fun parameter : ℂ => parameter - (3 : ℂ) / 2) (g := fun parameter => unitaryNormalize degree continuation parameter matrix)
    (x := (3 : ℂ) / 2) (analyticAt_id.sub analyticAt_const).meromorphicAt
    ((unitaryNormalize_continuation degree continuation_spec).1 matrix _)
  rw [meromorphicOrderAt_id_sub_const] at product_order
  rw [product_order] at equivalence
  have lower := normalized_continuation_boundary_order_ge_neg_one flat continuation_spec matrix
  by_cases top : meromorphicOrderAt
      (fun parameter => unitaryNormalize degree continuation parameter matrix) ((3 : ℂ) / 2) = ⊤
  · rw [top] at equivalence ⊢
    simp at equivalence
    exact ⟨fun _ => le_top, fun _ => equivalence⟩
  · lift meromorphicOrderAt (fun parameter => unitaryNormalize degree continuation parameter matrix)
      ((3 : ℂ) / 2) to ℤ using top with order equality
    have lower_int : (-1 : ℤ) ≤ order := WithTop.coe_le_coe.mp lower
    have equivalence_int : (1 : ℤ) + order = 0 ↔ normalizedBoundaryResidue degree continuation matrix ≠ 0 := by
      simpa only [← WithTop.coe_one, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] using equivalence
    rw [← not_iff_not] at equivalence_int
    simp only [not_not] at equivalence_int
    rw [← equivalence_int]
    norm_cast
    omega

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
