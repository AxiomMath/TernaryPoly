module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Helpers

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic MeasureTheory Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def localThreeIntegersCompacts : TopologicalSpace.PositiveCompacts ℚ_[3] where
  toCompacts := ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩
  interior_nonempty' := by
    refine ⟨0, ?_⟩
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))
      Metric.ball_subset_closedBall

def normalizedLocalThreeMeasure : Measure ℚ_[3] :=
  Measure.addHaarMeasure localThreeIntegersCompacts

theorem normalizedLocalThreeMeasure_haar : normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure localThreeIntegersCompacts

theorem normalizedLocalThreeMeasure_normalized :
    normalizedLocalThreeMeasure {scalar | ‖scalar‖ ≤ 1} = 1 := by
  have same_set : {scalar : ℚ_[3] | ‖scalar‖ ≤ 1} =
      (localThreeIntegersCompacts : Set ℚ_[3]) := by
    ext scalar
    change ‖scalar‖ ≤ 1 ↔ dist scalar 0 ≤ 1
    rw [dist_zero_right]
  rw [same_set]
  exact Measure.addHaarMeasure_self

theorem localBadPlaneSupport_left_translate
    (section_value : LocalThreeGL → ℂ)
    (support : LocalBadPlaneSupport section_value)
    (parabolic : planeParabolic ℚ_[3]) :
    LocalBadPlaneSupport (fun argument => section_value (parabolic.val * argument)) := by
  intro argument outside
  apply support
  rintro ⟨other_parabolic, compact, level, equality⟩
  apply outside
  refine ⟨parabolic⁻¹ * other_parabolic, compact, level, ?_⟩
  change argument = (parabolic.val⁻¹ * other_parabolic.val) * compact
  rw [mul_assoc, ← equality, inv_mul_cancel_left]

theorem localRightInvariant_left_translate
    (section_value : LocalThreeGL → ℂ)
    (invariant : LocalRightInvariant section_value)
    (parabolic : planeParabolic ℚ_[3]) :
    LocalRightInvariant (fun argument => section_value (parabolic.val * argument)) := by
  intro argument compact level
  change section_value (parabolic.val * (argument * compact)) =
    section_value (parabolic.val * argument)
  rw [← mul_assoc]
  exact invariant (parabolic.val * argument) compact level

def localBadPlaneSections : Submodule ℂ (LocalThreeGL → ℂ) where
  carrier := {section_value |
    LocalBadPlaneSupport section_value ∧ LocalRightInvariant section_value}
  zero_mem' := ⟨by intro argument outside; rfl, by intro argument compact level; rfl⟩
  add_mem' {first second} first_properties second_properties := by
    constructor
    · intro argument outside
      change first argument + second argument = 0
      rw [first_properties.1 argument outside, second_properties.1 argument outside,
        zero_add]
    · intro argument compact level
      change first (argument * compact) + second (argument * compact) =
        first argument + second argument
      rw [first_properties.2 argument compact level,
        second_properties.2 argument compact level]
  smul_mem' scalar section_value properties := by
    constructor
    · intro argument outside
      change scalar * section_value argument = 0
      rw [properties.1 argument outside, mul_zero]
    · intro argument compact level
      change scalar * section_value (argument * compact) = scalar * section_value argument
      rw [properties.2 argument compact level]

theorem localBadPlaneSections_eq_zero_of_parabolic_values
    (section_value : localBadPlaneSections)
    (vanishing : ∀ parabolic : planeParabolic ℚ_[3], section_value.val parabolic.val = 0) :
    section_value = 0 := by
  classical
  apply Subtype.ext
  funext argument
  by_cases supported : ∃ parabolic : planeParabolic ℚ_[3], ∃ compact : LocalThreeGL,
      InLocalThreeLevel compact ∧ argument = parabolic.val * compact
  · rcases supported with ⟨parabolic, compact, level, equality⟩
    change section_value.val argument = 0
    rw [equality, section_value.property.2 parabolic.val compact level]
    exact vanishing parabolic
  · exact section_value.property.1 argument supported

def localParabolicValues :
    localBadPlaneSections →ₗ[ℂ] (planeParabolic ℚ_[3] → ℂ) where
  toFun section_value parabolic := section_value.val parabolic.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem localParabolicValues_injective : Function.Injective localParabolicValues := by
  intro first second equality
  have difference_zero : first - second = 0 := by
    apply localBadPlaneSections_eq_zero_of_parabolic_values
    intro parabolic
    change first.val parabolic.val - second.val parabolic.val = 0
    exact sub_eq_zero.mpr (congrFun equality parabolic)
  exact sub_eq_zero.mp difference_zero

theorem localBadPlaneEntry_left_translate
    (local_entry : LocalBadPlaneEntry) (measure : Measure ℚ_[3])
    (haar : measure.IsAddHaarMeasure)
    (normalized : measure {scalar | ‖scalar‖ ≤ 1} = 1)
    (section_value : localBadPlaneSections) (parabolic : planeParabolic ℚ_[3]) :
    Integrable
      (localBadPlaneIntegrand (fun argument => section_value.val (parabolic.val * argument)))
      (measure.prod measure) ∧
    (∫ parameter,
      localBadPlaneIntegrand (fun argument => section_value.val (parabolic.val * argument))
        parameter ∂(measure.prod measure)) = (1 / 9 : ℂ) * section_value.val parabolic.val := by
  simpa only [mul_one] using local_entry measure haar normalized
    (fun argument => section_value.val (parabolic.val * argument))
    (localBadPlaneSupport_left_translate section_value.val section_value.property.1 parabolic)
    (localRightInvariant_left_translate section_value.val section_value.property.2 parabolic)

def localGoodLineEntries (measure : Measure ℚ_[3])
    (section_value : localBadPlaneSections) (parabolic : planeParabolic ℚ_[3]) : ℂ :=
  ∫ parameter,
    localBadPlaneIntegrand (fun argument => section_value.val (parabolic.val * argument))
      parameter ∂(measure.prod measure)

theorem localGoodLineEntries_eq
    (local_entry : LocalBadPlaneEntry) (measure : Measure ℚ_[3])
    (haar : measure.IsAddHaarMeasure)
    (normalized : measure {scalar | ‖scalar‖ ≤ 1} = 1)
    (section_value : localBadPlaneSections) :
    localGoodLineEntries measure section_value =
      (1 / 9 : ℂ) • localParabolicValues section_value := by
  funext parabolic
  exact (localBadPlaneEntry_left_translate local_entry measure haar normalized
    section_value parabolic).2

theorem localGoodLineEntries_injective
    (local_entry : LocalBadPlaneEntry) (measure : Measure ℚ_[3])
    (haar : measure.IsAddHaarMeasure)
    (normalized : measure {scalar | ‖scalar‖ ≤ 1} = 1) :
    Function.Injective (localGoodLineEntries measure) := by
  intro first second equality
  rw [localGoodLineEntries_eq local_entry measure haar normalized first,
    localGoodLineEntries_eq local_entry measure haar normalized second] at equality
  apply localParabolicValues_injective
  funext parabolic
  have pointwise := congrFun equality parabolic
  change (1 / 9 : ℂ) * first.val parabolic.val =
    (1 / 9 : ℂ) * second.val parabolic.val at pointwise
  exact mul_left_cancel₀ (by norm_num : (1 / 9 : ℂ) ≠ 0) pointwise

theorem localBadPlaneSections_eq_zero_of_goodLineEntries
    (local_entry : LocalBadPlaneEntry) (measure : Measure ℚ_[3])
    (haar : measure.IsAddHaarMeasure)
    (normalized : measure {scalar | ‖scalar‖ ≤ 1} = 1)
    (section_value : localBadPlaneSections)
    (vanishing : localGoodLineEntries measure section_value = 0) : section_value = 0 := by
  apply localBadPlaneSections_eq_zero_of_parabolic_values
  intro parabolic
  have integral_zero : localGoodLineEntries measure section_value parabolic = 0 :=
    congrFun vanishing parabolic
  simpa only [mul_one] using localBadPlaneEntry_detects_value local_entry measure haar normalized
    (fun argument => section_value.val (parabolic.val * argument))
    (localBadPlaneSupport_left_translate section_value.val section_value.property.1 parabolic)
    (localRightInvariant_left_translate section_value.val section_value.property.2 parabolic)
    integral_zero

theorem normalizedLocalGoodLineEntries_injective (local_entry : LocalBadPlaneEntry) :
    Function.Injective (localGoodLineEntries normalizedLocalThreeMeasure) :=
  localGoodLineEntries_injective local_entry normalizedLocalThreeMeasure
    normalizedLocalThreeMeasure_haar normalizedLocalThreeMeasure_normalized

end TernaryPeriodPolynomials.SphericalDetection.Helpers
