module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.PlaneDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

noncomputable def realPlanePeriodHom : Multiplicative (ℤ × ℤ) →* RealSL3 where
  toFun point := realSpecialPlane (3 * (point.toAdd.1 : ℝ)) (3 * (point.toAdd.2 : ℝ))
  map_one' := by
    change realSpecialPlane (3 * (0 : ℤ)) (3 * (0 : ℤ)) = 1
    simp only [Int.cast_zero, mul_zero, realSpecialPlane_zero]
  map_mul' first second := by
    rw [realSpecialPlane_add]
    change realSpecialPlane (3 * ((first.toAdd.1 + second.toAdd.1 : ℤ) : ℝ))
      (3 * ((first.toAdd.2 + second.toAdd.2 : ℤ) : ℝ)) = _
    simp only [Int.cast_add, mul_add]

noncomputable def realPlanePeriodSubgroup : Subgroup RealSL3 := realPlanePeriodHom.range

instance realPlanePeriodSubgroup_countable : Countable realPlanePeriodSubgroup := by
  let : Countable (Multiplicative (ℤ × ℤ)) := inferInstanceAs (Countable (ℤ × ℤ))
  exact Function.Surjective.countable realPlanePeriodHom.rangeRestrict_surjective

theorem realPlanePeriodSubgroup_le_parabolic : realPlanePeriodSubgroup ≤ principalRealPlaneParabolic := by
  rintro element ⟨point, rfl⟩
  exact principalRealPlaneUnipotent_mem point.toAdd.1 point.toAdd.2

def principalPlaneTube : Set RealSL3 := realPlaneBase ⁻¹' principalPlaneSliceDomain

theorem principalPlaneTube_measurable : MeasurableSet principalPlaneTube :=
  principalPlaneSliceDomain_measurable.preimage realPlaneBase_continuous.measurable

noncomputable def principalPlaneTubeMeasure : Measure RealSL3 :=
  realSpecialLinearHaar.restrict principalPlaneTube

theorem principalPlaneTube_preimage (first second : ℝ) :
    (fun matrix : RealSL3 => realSpecialPlane first second * matrix) ⁻¹' principalPlaneTube = principalPlaneTube := by
  ext matrix
  simp only [principalPlaneTube, Set.mem_preimage, realPlaneBase_pair_plane_mul]

theorem principalPlaneTube_translation (first second : ℝ) :
    MeasurePreserving (fun matrix : RealSL3 => realSpecialPlane first second * matrix)
      principalPlaneTubeMeasure principalPlaneTubeMeasure := by
  have preserving := (measurePreserving_mul_left realSpecialLinearHaar (realSpecialPlane first second)).restrict_preimage
    principalPlaneTube_measurable
  rw [principalPlaneTube_preimage] at preserving
  exact preserving

instance principalPlaneTubeMeasure_period_invariant :
    SMulInvariantMeasure realPlanePeriodSubgroup RealSL3 principalPlaneTubeMeasure := by
  constructor
  intro element set measurable
  obtain ⟨point, represents⟩ := element.property
  change principalPlaneTubeMeasure ((fun matrix => element.val * matrix) ⁻¹' set) = _
  rw [← represents]
  exact (principalPlaneTube_translation _ _).measure_preimage measurable.nullMeasurableSet

theorem principalPlaneTubeMeasure_restrict_domain :
    principalPlaneTubeMeasure.restrict principalPlaneDomain = realSpecialLinearHaar.restrict principalPlaneDomain := by
  rw [principalPlaneTubeMeasure, Measure.restrict_restrict principalPlaneDomain_measurable]
  congr 1
  exact Set.inter_eq_left.mpr (fun _ member => member.1)

theorem principalPlaneDomain_period_covers (matrix : RealSL3) (member : matrix ∈ principalPlaneTube) :
    ∃ element : realPlanePeriodSubgroup, element.val * matrix ∈ principalPlaneDomain := by
  obtain ⟨first, first_mem⟩ := integer_three_translate_mem_Ico (realPlaneCoordinate matrix 0)
  obtain ⟨second, second_mem⟩ := integer_three_translate_mem_Ico (realPlaneCoordinate matrix 1)
  let point : Multiplicative (ℤ × ℤ) := Multiplicative.ofAdd (first, second)
  refine ⟨⟨realPlanePeriodHom point, point, rfl⟩, ?_⟩
  change realPlaneBase (realSpecialPlane (3 * (first : ℝ)) (3 * (second : ℝ)) * matrix) ∈
    principalPlaneSliceDomain ∧
    realPlaneCoordinate (realSpecialPlane (3 * (first : ℝ)) (3 * (second : ℝ)) * matrix) 0 ∈ Set.Ico 0 3 ∧
    realPlaneCoordinate (realSpecialPlane (3 * (first : ℝ)) (3 * (second : ℝ)) * matrix) 1 ∈ Set.Ico 0 3
  rw [realPlaneBase_pair_plane_mul, realPlaneCoordinate_plane_mul_zero, realPlaneCoordinate_plane_mul_one]
  exact ⟨member, first_mem, second_mem⟩

theorem principalPlaneDomain_period_isFundamental :
    IsFundamentalDomain realPlanePeriodSubgroup principalPlaneDomain principalPlaneTubeMeasure := by
  apply IsFundamentalDomain.mk'' principalPlaneDomain_measurable.nullMeasurableSet
  · filter_upwards [ae_restrict_mem principalPlaneTube_measurable] with matrix member
    exact principalPlaneDomain_period_covers matrix member
  · intro element nonidentity
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro matrix image_member member
    obtain ⟨source, source_member, equality⟩ := image_member
    have identity := principalPlaneDomain_separated source matrix source_member member
      ⟨element.val, realPlanePeriodSubgroup_le_parabolic element.property⟩ equality
    apply nonidentity
    exact Subtype.ext (congrArg (fun value : principalRealPlaneParabolic => value.val) identity)
  · intro element
    exact (measurePreserving_smul element principalPlaneTubeMeasure).quasiMeasurePreserving

theorem realPlanePeriod_commute (element : realPlanePeriodSubgroup) (first second : ℝ) :
    realSpecialPlane first second * element.val = element.val * realSpecialPlane first second := by
  obtain ⟨point, represents⟩ := element.property
  rw [← represents]
  change realSpecialPlane first second * realSpecialPlane _ _ = realSpecialPlane _ _ * realSpecialPlane first second
  rw [realSpecialPlane_add, realSpecialPlane_add]
  congr 1 <;> ring

theorem principalPlaneDomain_translate_period_isFundamental (first second : ℝ) :
    IsFundamentalDomain realPlanePeriodSubgroup
      ((fun matrix : RealSL3 => realSpecialPlane first second * matrix) '' principalPlaneDomain)
        principalPlaneTubeMeasure := by
  let translation := MeasurableEquiv.mulLeft (realSpecialPlane first second)
  have inverse_preserving := MeasurePreserving.symm translation (principalPlaneTube_translation first second)
  apply principalPlaneDomain_period_isFundamental.image_of_equiv translation.toEquiv
    inverse_preserving.quasiMeasurePreserving (Equiv.refl realPlanePeriodSubgroup)
  intro element matrix
  change realSpecialPlane first second * (element.val * matrix) = element.val * (realSpecialPlane first second * matrix)
  rw [← mul_assoc, realPlanePeriod_commute, mul_assoc]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
