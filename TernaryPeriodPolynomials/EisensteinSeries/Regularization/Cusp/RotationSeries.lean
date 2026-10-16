module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationAdjoint

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem integer_inverse_square_summable : Summable (fun weight : ℤ => 1 / |(weight : ℝ)| ^ 2) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simp
  · simp

theorem cuspRotationProjection_norm_summable (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    Summable (fun weight : ℤ => ‖cuspRotationProjection cusp weight vector.val‖) := by
  have majorant := integer_inverse_square_summable.mul_left ‖((cuspRotationOperator cusp ^ 2) vector).val‖
  apply majorant.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with weight nonzero
  rw [norm_norm]
  have positive : 0 < |(weight : ℝ)| ^ 2 := by
    apply pow_pos
    exact abs_pos.mpr (by exact_mod_cast nonzero)
  have bound := cuspRotationProjection_weighted_norm_le cusp weight 2 vector
  calc
    _ ≤ ‖((cuspRotationOperator cusp ^ 2) vector).val‖ / |(weight : ℝ)| ^ 2 := by
      apply (le_div_iff₀ positive).mpr
      simpa only [mul_comm] using bound
    _ = _ := by ring

theorem cuspRotationProjection_summable (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    Summable (fun weight : ℤ => cuspRotationProjection cusp weight vector.val) :=
  (cuspRotationProjection_norm_summable cusp vector).of_norm

theorem cuspRotationProjection_tsum (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    (∑' weight : ℤ, cuspRotationProjection cusp weight vector.val) = vector.val := by
  classical
  have projections (weight : ℤ) :
      cuspRotationProjection cusp weight (∑' other : ℤ, cuspRotationProjection cusp other vector.val) =
        cuspRotationProjection cusp weight vector.val := by
    rw [(cuspRotationProjection cusp weight).map_tsum (cuspRotationProjection_summable cusp vector)]
    have term (other : ℤ) :
        cuspRotationProjection cusp weight (cuspRotationProjection cusp other vector.val) =
          if other = weight then cuspRotationProjection cusp other vector.val else 0 := by
      by_cases equal : other = weight
      · subst other
        simp only [ite_true, cuspRotationProjection_idempotent]
      · rw [ite_eq_right equal]
        exact cuspRotationProjection_distinct cusp other weight equal vector.val
    simp only [term, tsum_ite_eq]
  apply sub_eq_zero.mp
  apply cuspRotationProjection_complete cusp
  intro weight
  rw [map_sub, projections, sub_self]

theorem cuspRotationProjection_hasSum (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    HasSum (fun weight : ℤ => cuspRotationProjection cusp weight vector.val) vector.val := by
  simpa only [cuspRotationProjection_tsum cusp vector] using (cuspRotationProjection_summable cusp vector).hasSum

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
