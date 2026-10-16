module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.TaylorBounds

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open Filter Topology
open scoped NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TaylorFamilies

open CompactTaylorBounds

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem weaken {function : E → F} {center : E} {radius oldRadius : ℝ≥0}
    {constant oldConstant : ℝ} (positive : 0 < radius) (radiusLe : radius ≤ oldRadius)
    (nonnegative : 0 ≤ oldConstant) (constantLe : oldConstant ≤ constant)
    (bounded : HasFPowerSeriesOnBall function (coefficients function center) center oldRadius ∧
      ∀ order, ‖coefficients function center order‖ ≤ oldConstant * (oldRadius : ℝ)⁻¹ ^ order) :
    HasFPowerSeriesOnBall function (coefficients function center) center radius ∧
      ∀ order, ‖coefficients function center order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
  refine ⟨bounded.1.mono (by exact_mod_cast positive) (by exact_mod_cast radiusLe), ?_⟩
  intro order
  apply (bounded.2 order).trans
  have inverseLe : (oldRadius : ℝ)⁻¹ ≤ (radius : ℝ)⁻¹ := by
    apply (inv_le_inv₀ (by exact_mod_cast positive.trans_le radiusLe)
      (by exact_mod_cast positive)).mpr
    exact_mod_cast radiusLe
  exact mul_le_mul constantLe
    (pow_le_pow_left₀ (inv_nonneg.mpr oldRadius.property) inverseLe order)
    (pow_nonneg (inv_nonneg.mpr oldRadius.property) _) (nonnegative.trans constantLe)

theorem restrict_snd {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {function : G × E → F} {series : FormalMultilinearSeries ℝ (G × E) F}
    {first : G} {center : E} {radius : ℝ≥0} (positive : 0 < radius)
    (expansion : HasFPowerSeriesOnBall function series (first, center) radius)
    (constant : ℝ)
    (bound : ∀ order, ‖series order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order) :
    HasFPowerSeriesOnBall (fun point => function (first, point))
        (coefficients (fun point => function (first, point)) center) center radius ∧
      ∀ order, ‖coefficients (fun point => function (first, point)) center order‖ ≤
        constant * (radius : ℝ)⁻¹ ^ order := by
  let inclusion := ContinuousLinearMap.inr ℝ G E
  let restricted := series.compContinuousLinearMap inclusion
  have restrictedBound (order : ℕ) :
      ‖restricted order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
    apply le_trans ((series order).norm_compContinuousLinearMap_le (fun _ => inclusion))
    have productLe : (∏ _ : Fin order, ‖inclusion‖) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ =>
        ContinuousLinearMap.norm_inr_le_one ℝ G E)
    exact (mul_le_of_le_one_right (norm_nonneg _) productLe).trans (bound order)
  have restrictedExpansion : HasFPowerSeriesOnBall (fun point => function (first, point))
      restricted center radius := by
    refine ⟨radius_of_coefficient_bound _ radius positive constant restrictedBound,
      by exact_mod_cast positive, ?_⟩
    intro offset membership
    have pairMembership : (0, offset) ∈ Metric.eball (0 : G × E) radius := by
      simpa [Metric.eball_coe, Metric.mem_ball, dist_eq_norm, Prod.norm_def] using membership
    simpa [restricted, inclusion, FormalMultilinearSeries.compContinuousLinearMap_apply,
      Function.comp_def] using expansion.hasSum pairMembership
  have canonicalBound (order : ℕ) :=
    (coefficients_norm_le restrictedExpansion order).trans (restrictedBound order)
  exact ⟨canonical_expansion positive restrictedExpansion constant canonicalBound, canonicalBound⟩

theorem congr {function other : E → F} {center : E} {radius : ℝ≥0}
    (positive : 0 < radius) (constant : ℝ)
    (bounded : HasFPowerSeriesOnBall function (coefficients function center) center radius ∧
      ∀ order, ‖coefficients function center order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order)
    (agrees : Set.EqOn function other (Metric.ball center radius)) :
    HasFPowerSeriesOnBall other (coefficients other center) center radius ∧
      ∀ order, ‖coefficients other center order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
  have expansion := bounded.1.congr (by simpa only [Metric.eball_coe] using agrees)
  have bound (order : ℕ) := (coefficients_norm_le expansion order).trans (bounded.2 order)
  exact ⟨canonical_expansion positive expansion constant bound, bound⟩

omit [CompleteSpace F] in
theorem map {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {function : E → F} {center : E} {radius : ℝ≥0}
    (positive : 0 < radius) (constant : ℝ)
    (bounded : HasFPowerSeriesOnBall function (coefficients function center) center radius ∧
      ∀ order, ‖coefficients function center order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order)
    (linear : F →L[ℝ] G) (factor : ℝ) (factorNonnegative : 0 ≤ factor)
    (linearBound : ‖linear‖ ≤ factor) :
    HasFPowerSeriesOnBall (linear ∘ function) (coefficients (linear ∘ function) center) center radius ∧
      ∀ order, ‖coefficients (linear ∘ function) center order‖ ≤
        (factor * constant) * (radius : ℝ)⁻¹ ^ order := by
  have expansion := linear.comp_hasFPowerSeriesOnBall bounded.1
  have bound (order : ℕ) : ‖coefficients (linear ∘ function) center order‖ ≤
      (factor * constant) * (radius : ℝ)⁻¹ ^ order := by
    apply (coefficients_norm_le expansion order).trans
    apply (linear.norm_compContinuousMultilinearMap_le (coefficients function center order)).trans
    exact (mul_le_mul linearBound (bounded.2 order) (norm_nonneg _) factorNonnegative).trans_eq
      (mul_assoc _ _ _).symm
  exact ⟨canonical_expansion positive expansion _ bound, bound⟩

omit [CompleteSpace F] in
theorem uniform_on_compact {A : Type} [TopologicalSpace A] (family : A → E → F)
    (center : E) (compact : Set A) (compactness : IsCompact compact)
    (locally : ∀ point ∈ compact, ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ,
      0 ≤ constant ∧ ∀ᶠ argument in 𝓝 point,
        HasFPowerSeriesOnBall (family argument) (coefficients (family argument) center) center radius ∧
        ∀ order, ‖coefficients (family argument) center order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ argument ∈ compact,
        HasFPowerSeriesOnBall (family argument) (coefficients (family argument) center) center radius ∧
        ∀ order, ‖coefficients (family argument) center order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
  let property := fun set : Set A => ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ,
    0 ≤ constant ∧ ∀ argument ∈ set,
      HasFPowerSeriesOnBall (family argument) (coefficients (family argument) center) center radius ∧
      ∀ order, ‖coefficients (family argument) center order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order
  change property compact
  apply compactness.induction_on (p := property)
  · exact ⟨1, zero_lt_one, 0, le_rfl, by simp⟩
  · intro small large inclusion larger
    obtain ⟨radius, positive, constant, nonnegative, bounded⟩ := larger
    exact ⟨radius, positive, constant, nonnegative, fun point member => bounded point (inclusion member)⟩
  · intro first second firstProperty secondProperty
    obtain ⟨firstRadius, firstPositive, firstConstant, firstNonnegative, firstBound⟩ := firstProperty
    obtain ⟨secondRadius, secondPositive, secondConstant, secondNonnegative, secondBound⟩ := secondProperty
    refine ⟨min firstRadius secondRadius, lt_min firstPositive secondPositive,
      max firstConstant secondConstant, firstNonnegative.trans (le_max_left _ _), ?_⟩
    intro point member
    rcases member with member | member
    · exact weaken (lt_min firstPositive secondPositive) (min_le_left _ _) firstNonnegative
        (le_max_left _ _) (firstBound point member)
    · exact weaken (lt_min firstPositive secondPositive) (min_le_right _ _) secondNonnegative
        (le_max_right _ _) (secondBound point member)
  · intro point member
    obtain ⟨radius, positive, constant, nonnegative, bounded⟩ := locally point member
    exact ⟨_, nhdsWithin_le_nhds bounded, radius, positive, constant, nonnegative,
      fun _ membership => membership⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TaylorFamilies
