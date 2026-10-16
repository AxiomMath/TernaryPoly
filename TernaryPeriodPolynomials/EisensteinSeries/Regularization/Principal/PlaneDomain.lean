module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.PlaneFactorization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem integer_three_translate_mem_Ico (value : ℝ) :
    ∃ integer : ℤ, 3 * (integer : ℝ) + value ∈ Set.Ico (0 : ℝ) 3 := by
  refine ⟨-⌊value / 3⌋, ?_, ?_⟩
  · push_cast
    linarith [Int.floor_le (value / 3)]
  · push_cast
    linarith [Int.lt_floor_add_one (value / 3)]

theorem integer_three_translate_unique (first second : ℝ) (integer : ℤ)
    (first_mem : first ∈ Set.Ico (0 : ℝ) 3) (second_mem : second ∈ Set.Ico (0 : ℝ) 3)
    (relation : 3 * (integer : ℝ) + first = second) : integer = 0 := by
  by_contra nonzero
  rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ nonzero with negative | positive
  · linarith [first_mem.1, first_mem.2, second_mem.1, second_mem.2]
  · linarith [first_mem.1, first_mem.2, second_mem.1, second_mem.2]

theorem principalRealPlaneUnipotent_mem (first second : ℤ) :
    realSpecialPlane (3 * (first : ℝ)) (3 * (second : ℝ)) ∈ principalRealPlaneParabolic := by
  refine ⟨?_, ?_⟩
  · refine ⟨specialLinearPlaneUnipotent (3 * first) (3 * second),
      principalIntegerPlaneUnipotent_mem first second, ?_⟩
    rw [specialLinearPlaneUnipotent_map, specialLinearPlaneUnipotent_real]
    norm_cast
  · exact ⟨rfl, rfl⟩

theorem principalRealPlaneLevi_le_parabolic : principalRealPlaneLevi ≤ principalRealPlaneParabolic := by
  intro element member
  refine ⟨member.1, ?_⟩
  obtain ⟨binary, represents⟩ := member.2
  rw [← represents]
  exact ⟨rfl, rfl⟩

theorem principalRealPlaneLevi_base_mul (element : principalRealPlaneLevi) (matrix : RealSL3) :
    realPlaneBase (element.val * matrix) = element.val * realPlaneBase matrix := by
  obtain ⟨binary, represents⟩ := element.property.2
  rw [← represents]
  exact realPlaneBase_levi_mul binary matrix

def principalPlaneDomain : Set RealSL3 :=
  {matrix | realPlaneBase matrix ∈ principalPlaneSliceDomain ∧
    realPlaneCoordinate matrix 0 ∈ Set.Ico (0 : ℝ) 3 ∧
      realPlaneCoordinate matrix 1 ∈ Set.Ico (0 : ℝ) 3}

theorem principalPlaneDomain_measurable : MeasurableSet principalPlaneDomain :=
  (principalPlaneSliceDomain_measurable.preimage realPlaneBase_continuous.measurable).inter
    ((measurableSet_Ico.preimage (realPlaneCoordinate_continuous 0).measurable).inter
      (measurableSet_Ico.preimage (realPlaneCoordinate_continuous 1).measurable))

theorem principalPlaneDomain_covers (matrix : RealSL3) :
    ∃ element : principalRealPlaneParabolic, element.val * matrix ∈ principalPlaneDomain := by
  obtain ⟨levi, base_member, _⟩ := principalPlaneSliceDomain_unique (realPlaneBase matrix)
    (realPlaneBase_mem_normalSet matrix)
  obtain ⟨first, first_member⟩ := integer_three_translate_mem_Ico (realPlaneCoordinate (levi.val * matrix) 0)
  obtain ⟨second, second_member⟩ := integer_three_translate_mem_Ico (realPlaneCoordinate (levi.val * matrix) 1)
  let unipotent := realSpecialPlane (3 * (first : ℝ)) (3 * (second : ℝ))
  let element : principalRealPlaneParabolic := ⟨unipotent * levi.val,
    principalRealPlaneParabolic.mul_mem (principalRealPlaneUnipotent_mem first second)
      (principalRealPlaneLevi_le_parabolic levi.property)⟩
  refine ⟨element, ?_⟩
  change realPlaneBase ((unipotent * levi.val) * matrix) ∈ principalPlaneSliceDomain ∧ _
  rw [mul_assoc]
  have base := realPlaneBase_plane_mul ![3 * (first : ℝ), 3 * (second : ℝ)] (levi.val * matrix)
  refine ⟨?_, ?_, ?_⟩
  · rw [show realPlaneBase (unipotent * (levi.val * matrix)) = realPlaneBase (levi.val * matrix) from base,
      principalRealPlaneLevi_base_mul]
    exact base_member
  · simpa only [unipotent, realPlaneCoordinate_plane_mul_zero] using first_member
  · simpa only [unipotent, realPlaneCoordinate_plane_mul_one] using second_member

theorem principalPlaneDomain_separated (first second : RealSL3)
    (first_member : first ∈ principalPlaneDomain) (second_member : second ∈ principalPlaneDomain)
    (element : principalRealPlaneParabolic) (relation : element.val * first = second) : element = 1 := by
  obtain ⟨a, b, levi, factorization⟩ := principalRealPlaneParabolic_factorization element
  have base_relation : levi.val * realPlaneBase first = realPlaneBase second := by
    rw [← relation, factorization, mul_assoc]
    rw [realPlaneBase_pair_plane_mul, principalRealPlaneLevi_base_mul]
  have levi_one : levi = 1 := by
    obtain ⟨chosen, _, unique⟩ := principalPlaneSliceDomain_unique (realPlaneBase first)
      (realPlaneBase_mem_normalSet first)
    have identity_mem : (1 : principalRealPlaneLevi).val * realPlaneBase first ∈ principalPlaneSliceDomain := by
      simpa using first_member.1
    have levi_mem : levi.val * realPlaneBase first ∈ principalPlaneSliceDomain := by
      rw [base_relation]
      exact second_member.1
    exact (unique levi levi_mem).trans (unique 1 identity_mem).symm
  have relation' : realSpecialPlane (3 * (a : ℝ)) (3 * (b : ℝ)) * first = second := by
    rw [factorization, levi_one, Subgroup.coe_one, mul_one] at relation
    exact relation
  have coord0 := realPlaneCoordinate_plane_mul_zero (3 * (a : ℝ)) (3 * (b : ℝ)) first
  have coord1 := realPlaneCoordinate_plane_mul_one (3 * (a : ℝ)) (3 * (b : ℝ)) first
  rw [relation'] at coord0 coord1
  have a_zero := integer_three_translate_unique _ _ a first_member.2.1 second_member.2.1 coord0.symm
  have b_zero := integer_three_translate_unique _ _ b first_member.2.2 second_member.2.2 coord1.symm
  apply Subtype.ext
  simpa only [a_zero, b_zero, Int.cast_zero, mul_zero, realSpecialPlane_zero, levi_one,
    Subgroup.coe_one, one_mul] using factorization

theorem principalPlaneDomain_unique (matrix : RealSL3) :
    ∃! element : principalRealPlaneParabolic, element.val * matrix ∈ principalPlaneDomain := by
  obtain ⟨element, member⟩ := principalPlaneDomain_covers matrix
  refine ⟨element, member, ?_⟩
  intro other other_member
  have identity := principalPlaneDomain_separated _ _ member other_member (other * element⁻¹)
    (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left])
  exact mul_inv_eq_one.mp identity

theorem principalPlaneDomain_isFundamental :
    IsFundamentalDomain principalRealPlaneParabolic principalPlaneDomain realSpecialLinearHaar :=
  IsFundamentalDomain.mk' principalPlaneDomain_measurable.nullMeasurableSet principalPlaneDomain_unique

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
