module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.BoundaryBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ContinuationGerms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_continuation_boundary_product_order
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (matrix : AdelicGL) :
    0 ≤ meromorphicOrderAt (fun parameter => (parameter - (3 : ℂ) / 2) *
      unitaryNormalize degree continuation parameter matrix) ((3 : ℂ) / 2) := by
  obtain ⟨bound, _, bounded⟩ := normalized_scalar_sum_compact_boundary_bound flat {matrix} isCompact_singleton
  apply nonnegative_order_of_bounded_real_ray
  refine ⟨bound, ?_⟩
  filter_upwards [bounded, normalized_continuation_boundary_ray_eq_actual_sum flat continuation_spec matrix,
    self_mem_nhdsWithin] with displacement bounded same positive
  change 0 < displacement at positive
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive, same]
  exact bounded matrix (Set.mem_singleton matrix)

theorem normalized_continuation_boundary_order_ge_neg_one
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (matrix : AdelicGL) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (fun parameter => unitaryNormalize degree continuation parameter matrix) ((3 : ℂ) / 2) := by
  have product_order := normalized_continuation_boundary_product_order flat continuation_spec matrix
  have shift_meromorphic : MeromorphicAt (fun parameter : ℂ => parameter - (3 : ℂ) / 2) ((3 : ℂ) / 2) :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  rw [fun_meromorphicOrderAt_mul shift_meromorphic
      ((unitaryNormalize_continuation degree continuation_spec).1 matrix _),
    meromorphicOrderAt_id_sub_const] at product_order
  by_cases top : meromorphicOrderAt
      (fun parameter => unitaryNormalize degree continuation parameter matrix) ((3 : ℂ) / 2) = ⊤
  · rw [top]
    exact le_top
  · lift meromorphicOrderAt (fun parameter => unitaryNormalize degree continuation parameter matrix)
      ((3 : ℂ) / 2) to ℤ using top with order equality
    norm_cast at product_order
    exact WithTop.coe_le_coe.mpr (by omega : (-1 : ℤ) ≤ order)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
