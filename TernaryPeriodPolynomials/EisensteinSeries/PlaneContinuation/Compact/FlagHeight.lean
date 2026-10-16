module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RowActionContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.Height
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.Continuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarParameter TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicHeight

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFlagHeight

theorem determinant_log_continuous :
    Continuous (fun matrix : RealGL3 => Real.log |matrix.val.det| / 3) := by
  apply Continuous.div_const
  apply Continuous.log Units.continuous_val.matrix_det.abs
  intro matrix
  exact abs_ne_zero.mpr ((Matrix.isUnit_iff_isUnit_det _).mp matrix.isUnit).ne_zero

theorem finite_bound (points : Set FiniteGL) (compact : IsCompact points) :
    ∃ bound : ℝ, ∀ point ∈ points, ∀ matrix ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact,
      height (atFinite (matrix * point)) ≤ bound := by
  obtain ⟨bound, bounded⟩ := (TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact_isCompact.prod compact).exists_bound_of_continuousOn
    (finite_height_continuous.comp (continuous_fst.mul continuous_snd)).continuousOn
  exact ⟨bound, fun point membership matrix matrixMembership =>
    (le_abs_self _).trans (bounded (matrix, point) ⟨matrixMembership, membership⟩)⟩

theorem height_bound (points : Set AdelicGL) (compact : IsCompact points) :
    ∃ bound : ℝ, ∀ point ∈ points, ∀ flag : Flags .plane,
      height (rationalGroup flag.out⁻¹ * point) ≤ bound - Real.log (flagRadius flag) := by
  obtain ⟨finiteBound, finiteBounded⟩ := finite_bound (finiteGroup '' points)
    (compact.image TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedContinuity.finiteGroup_continuous)
  have realCompact := compact.image TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedContinuity.realGroup_continuous
  obtain ⟨distortion, distortionPositive, distorted⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowActionContinuity.exists_distortion_bound (realGroup '' points) realCompact
  obtain ⟨detBound, detBounded⟩ := realCompact.exists_bound_of_continuousOn determinant_log_continuous.continuousOn
  refine ⟨detBound + Real.log distortion + finiteBound, fun point membership flag => ?_⟩
  have sameFlag : (QuotientGroup.mk flag.out : Flags .plane) = QuotientGroup.mk
      (integralRational (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)) := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative_mk]
    exact Quotient.out_eq flag
  rw [height_eq_of_flag _ _ sameFlag, ← map_inv, height_integral_product]
  have finiteInequality := finiteBounded (finiteGroup point) ⟨point, membership, rfl⟩
    (integralFinite (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹)
    ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹,
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralFinite_eq_map _).symm⟩
  have detInequality := (le_abs_self (Real.log |(realGroup point).val.det| / 3)).trans
    (detBounded (realGroup point) ⟨point, membership, rfl⟩)
  let vector : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2
    (fun column => (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ))
  have rowBound : flagRadius flag ≤ distortion * ‖TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowAction.rowAction (realGroup point) vector‖ :=
    distorted (realGroup point) ⟨point, membership, rfl⟩ vector
  have rowPositive : 0 < ‖TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowAction.rowAction (realGroup point) vector‖ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds.lastRow_norm_pos
      (GeneralLinearGroup.map (Int.castRingHom ℝ)
        (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹ * realGroup point)
  have logarithm := Real.log_le_log (flagRadius_pos flag) rowBound
  rw [Real.log_mul distortionPositive.ne' rowPositive.ne'] at logarithm
  change Real.log |(realGroup point).val.det| / 3 -
    Real.log ‖TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowAction.rowAction (realGroup point) vector‖ +
    height (atFinite (integralFinite (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹ * finiteGroup point)) ≤ _
  linarith

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFlagHeight
