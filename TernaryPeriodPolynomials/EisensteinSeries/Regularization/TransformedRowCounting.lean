module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.TransformedRowLattice
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.CountingPowerBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cube_norm_unit_sublevel :
    {vector : Fin 3 → ℝ | vector ∈ (Set.univ : Set (Fin 3 → ℝ)) ∧ ‖vector‖ ^ 3 ≤ 1} =
      Metric.closedBall 0 1 := by
  ext vector
  simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro bound
    nlinarith [norm_nonneg vector, sq_nonneg (‖vector‖ - 1)]
  · intro bound
    exact (pow_le_pow_left₀ (norm_nonneg vector) bound 3).trans_eq (by norm_num)

theorem transformedRowLattice_cube_count_tendsto (matrix : RealGL3) :
    Tendsto (fun value : ℝ =>
      (Nat.card ({vector : Fin 3 → ℝ | ‖vector‖ ^ 3 ≤ value} ∩
        (transformedRowLattice matrix : Set (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) : ℝ) / value)
      atTop (nhds (volume.real (Metric.closedBall (0 : Fin 3 → ℝ) 1) / |matrix.val.det|)) := by
  have limit := ZLattice.covolume.tendsto_card_le_div (transformedRowLattice matrix)
    (X := Set.univ) (F := fun vector => ‖vector‖ ^ 3)
    (by intros; trivial) (by
      intro vector scalar nonnegative
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg nonnegative, mul_pow, Fintype.card_fin])
    (by rw [cube_norm_unit_sublevel]; exact Metric.isBounded_closedBall)
    (by rw [cube_norm_unit_sublevel]; exact measurableSet_closedBall)
    (by rw [cube_norm_unit_sublevel]; exact (convex_closedBall (0 : Fin 3 → ℝ) 1).addHaar_frontier volume)
  rw [cube_norm_unit_sublevel, transformedRowLattice_covolume] at limit
  simpa only [Set.mem_univ, true_and] using limit

noncomputable def transformedRowClosedBallEquiv (matrix : RealGL3) (radius : ℝ) (nonnegative : 0 ≤ radius) :
    {vector : transformedRowLattice matrix // ‖vector‖ ≤ radius} ≃
      ({vector : Fin 3 → ℝ | ‖vector‖ ^ 3 ≤ radius ^ 3} ∩
        (transformedRowLattice matrix : Set (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) where
  toFun vector := ⟨vector.val.val,
    pow_le_pow_left₀ (norm_nonneg vector.val) vector.property 3, vector.val.property⟩
  invFun vector := ⟨⟨vector.val, vector.property.2⟩, by
    have bound := vector.property.1
    change ‖vector.val‖ ^ 3 ≤ radius ^ 3 at bound
    change ‖vector.val‖ ≤ radius
    exact le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) nonnegative bound⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem transformedRowLattice_ball_count_tendsto (matrix : RealGL3) :
    Tendsto (fun radius : ℝ =>
      (({vector : transformedRowLattice matrix | ‖vector‖ ≤ radius}.ncard : ℕ) : ℝ) / radius ^ 3)
      atTop (nhds (volume.real (Metric.closedBall (0 : Fin 3 → ℝ) 1) / |matrix.val.det|)) := by
  have cubed : Tendsto (fun radius : ℝ => radius ^ 3) atTop atTop := tendsto_pow_atTop (by decide)
  have limit := (transformedRowLattice_cube_count_tendsto matrix).comp cubed
  apply limit.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with radius nonnegative
  dsimp only [Function.comp_def]
  rw [← Nat.card_congr (transformedRowClosedBallEquiv matrix radius nonnegative)]
  rfl

theorem transformedRowLattice_nonzero_ball_finite (matrix : RealGL3) (radius : ℝ) :
    {vector : {vector : transformedRowLattice matrix // vector ≠ 0} | ‖vector.val‖ < radius}.Finite := by
  exact (transformedRowLattice_finite_ball matrix radius).preimage Subtype.val_injective.injOn

theorem transformedRowLattice_nonzero_count_bound (matrix : RealGL3) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∀ radius : ℝ, threshold < radius →
      (({vector : {vector : transformedRowLattice matrix // vector ≠ 0} | ‖vector.val‖ < radius}.ncard : ℕ) : ℝ) ≤
        (volume.real (Metric.closedBall (0 : Fin 3 → ℝ) 1) / |matrix.val.det| + 1) * radius ^ 3 := by
  have upper := (transformedRowLattice_ball_count_tendsto matrix).eventually
    (gt_mem_nhds (lt_add_one (volume.real (Metric.closedBall (0 : Fin 3 → ℝ) 1) / |matrix.val.det|)))
  obtain ⟨threshold, upper⟩ := eventually_atTop.mp upper
  refine ⟨max 1 threshold, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro radius radius_large
  have radius_positive : 0 < radius := lt_trans (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) radius_large
  have finite_closed : {vector : transformedRowLattice matrix | ‖vector‖ ≤ radius}.Finite :=
    (transformedRowLattice_finite_ball matrix (radius + 1)).subset (by intro vector member; exact lt_of_le_of_lt member (lt_add_one radius))
  have count_le : {vector : {vector : transformedRowLattice matrix // vector ≠ 0} | ‖vector.val‖ < radius}.ncard ≤
      {vector : transformedRowLattice matrix | ‖vector‖ ≤ radius}.ncard := by
    let inclusion : {vector : {vector : transformedRowLattice matrix // vector ≠ 0} // ‖vector.val‖ < radius} →
        {vector : transformedRowLattice matrix // ‖vector‖ ≤ radius} := fun vector => ⟨vector.val.val, vector.property.le⟩
    have injective : Function.Injective inclusion := by
      intro first second equality
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun vector : {vector : transformedRowLattice matrix // ‖vector‖ ≤ radius} => vector.val) equality
    let : Fintype {vector : transformedRowLattice matrix // ‖vector‖ ≤ radius} := finite_closed.fintype
    have comparison := Nat.card_le_card_of_injective inclusion injective
    exact comparison
  have estimate := (div_le_iff₀ (pow_pos radius_positive 3)).mp
    (upper radius (le_of_lt ((le_max_right _ _).trans_lt radius_large))).le
  exact (Nat.cast_le.mpr count_le).trans estimate

theorem transformedRowLattice_boundary_power_bound (matrix : RealGL3) :
    ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      displacement * (∑' vector : {vector : transformedRowLattice matrix // vector ≠ 0},
        ‖vector.val‖ ^ (-3 - displacement)) ≤
      3 * (volume.real (Metric.closedBall (0 : Fin 3 → ℝ) 1) / |matrix.val.det| + 1) + 1 := by
  obtain ⟨threshold, positive, bound⟩ := transformedRowLattice_nonzero_count_bound matrix
  exact power_tsum_boundary_bound_of_counting (fun vector : {vector : transformedRowLattice matrix // vector ≠ 0} => ‖vector.val‖)
    (fun vector => norm_pos_iff.mpr vector.property) (transformedRowLattice_nonzero_ball_finite matrix)
    threshold _ positive bound

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
