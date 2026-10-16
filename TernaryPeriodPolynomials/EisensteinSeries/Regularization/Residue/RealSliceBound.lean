module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.TransformedRowCounting
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.Residue

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def planeFlagTransformedRow (matrix : RealGL3) (flag : Flags .plane) :
    {vector : transformedRowLattice matrix // vector ≠ 0} :=
  ⟨transformedRowEquiv matrix (planeFlagIntegerRow flag), by
    intro zero
    apply planeFlagIntegerRow_ne_zero flag
    apply (transformedRowEquiv matrix).injective
    simpa only [map_zero] using zero⟩

theorem planeFlagTransformedRow_injective (matrix : RealGL3) : Function.Injective (planeFlagTransformedRow matrix) := by
  intro first second equality
  apply planeFlagIntegerRow_injective
  apply (transformedRowEquiv matrix).injective
  exact congrArg (fun vector : {vector : transformedRowLattice matrix // vector ≠ 0} => vector.val) equality

theorem planeFlagTransformedRow_norm (matrix : RealGL3) (flag : Flags .plane) :
    ‖(planeFlagTransformedRow matrix flag).val‖ =
      ‖(fun index => (planeFlagIntegerRow flag index : ℝ)) ᵥ* matrix.val‖ := by
  change ‖(transformedRowEquiv matrix (planeFlagIntegerRow flag)).val‖ = _
  rw [transformedRowEquiv_val]

theorem transformedRowLattice_nonzero_power_summable (matrix : RealGL3) (displacement : ℝ)
    (positive : 0 < displacement) :
    Summable (fun vector : {vector : transformedRowLattice matrix // vector ≠ 0} =>
      ‖vector.val‖ ^ (-3 - displacement)) := by
  have small : -3 - displacement < -(Module.finrank ℤ (transformedRowLattice matrix) : ℝ) := by
    rw [Module.finrank_eq_card_basis (transformedRowLatticeBasis matrix)]
    norm_num
    linarith
  exact (ZLattice.summable_norm_rpow (transformedRowLattice matrix) (-3 - displacement) small).subtype (fun vector => vector ≠ 0)

theorem normalizedBoundaryResidue_unitDet_integral_bound
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ matrix : AdelicGL,
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding) →
      |(realGroup matrix).val.det| = 1 → ‖normalizedBoundaryResidue degree continuation matrix‖ ≤ bound := by
  obtain ⟨coefficient, nonnegative, estimate⟩ := normalized_scalar_flag_transformed_row_bound flat
  let latticeBound : ℝ := 3 * (volume.real (Metric.closedBall (0 : Fin 3 → ℝ) 1) + 1) + 1
  refine ⟨latticeBound * coefficient, mul_nonneg (by dsimp [latticeBound]; positivity) nonnegative, ?_⟩
  intro matrix integral unit_det
  have lattice_bound := transformedRowLattice_boundary_power_bound (realGroup matrix)
  rw [unit_det, div_one] at lattice_bound
  apply le_of_tendsto (normalizedBoundaryResidue_tendsto flat continuation_spec matrix).norm
  filter_upwards [lattice_bound, self_mem_nhdsWithin] with displacement lattice_bound positive
  change 0 < displacement at positive
  have parameter_large : 3 / 2 < ((3 : ℂ) / 2 + (displacement : ℂ)).re := by norm_num; exact positive
  have exponent : -(3 / 2 + ((3 : ℂ) / 2 + (displacement : ℂ)).re) = -3 - displacement := by norm_num; ring
  have term_bound (flag : Flags .plane) :
      ‖eisensteinSummand (unitaryNormalize degree family) ((3 : ℂ) / 2 + (displacement : ℂ)) matrix flag‖ ≤
        ‖(planeFlagTransformedRow (realGroup matrix) flag).val‖ ^ (-3 - displacement) * coefficient := by
    have bounded := estimate ((3 : ℂ) / 2 + (displacement : ℂ)) (by linarith) matrix integral flag
    rw [unit_det, Real.one_rpow, one_mul, exponent, ← planeFlagTransformedRow_norm] at bounded
    exact bounded
  have norm_summable := ((normalized_scalar_sum_analytic flat matrix).2 _ parameter_large).norm
  have lattice_summable := (transformedRowLattice_nonzero_power_summable (realGroup matrix) displacement positive).mul_right coefficient
  have sum_bound := (norm_tsum_le_tsum_norm norm_summable).trans
    (Summable.tsum_le_tsum_of_inj (planeFlagTransformedRow (realGroup matrix))
      (planeFlagTransformedRow_injective (realGroup matrix))
      (fun vector _ => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) nonnegative)
      term_bound norm_summable lattice_summable)
  rw [tsum_mul_right] at sum_bound
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ displacement * ((∑' vector : {vector : transformedRowLattice (realGroup matrix) // vector ≠ 0},
        ‖vector.val‖ ^ (-3 - displacement)) * coefficient) :=
      mul_le_mul_of_nonneg_left sum_bound positive.le
    _ = (displacement * (∑' vector : {vector : transformedRowLattice (realGroup matrix) // vector ≠ 0},
        ‖vector.val‖ ^ (-3 - displacement))) * coefficient := by ring
    _ ≤ latticeBound * coefficient := mul_le_mul_of_nonneg_right lattice_bound nonnegative

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
