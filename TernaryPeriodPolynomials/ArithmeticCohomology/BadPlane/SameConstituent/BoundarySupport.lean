module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.SupportCutoff

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers

noncomputable section
attribute [local instance] Classical.propDecidable

theorem good_flag_arithmetic (translate : arithmeticLevel) {flag : Flags .plane}
    (flag_good : GoodFlag .plane flag) :
    GoodFlag .plane (rationalInclusion translate • flag) := by
  obtain ⟨vector, ⟨frame, frame_flag, coordinates, coordinates_last, vector_eq⟩,
    last_nonzero⟩ := flag_good
  refine ⟨translate.val.val *ᵥ vector,
    ⟨rationalInclusion translate * frame, ?_, coordinates, coordinates_last, ?_⟩, ?_⟩
  · rw [← frame_flag]
    rfl
  · rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, vector_eq]
    change (translate.val.val.map (Int.castRingHom ℚ)) *ᵥ
      (fun index => (vector index : ℚ)) = _
    exact (map_mulVec_eq (Int.castRingHom ℚ) translate.val.val vector).symm
  · have row : lastRow ᵥ* (reductionThree translate.val).val = lastRow := translate.property
    have row_entry (index : Fin 3) :
        (translate.val.val 2 index : ZMod 3) = lastRow index := by
      have entry := congrFun row index
      simpa [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
        reductionThree, GeneralLinearGroup.map_apply] using entry
    simpa [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, row_entry,
      lastRow, Fin.sum_univ_three] using last_nonzero

theorem good_flag_level_forward (translate : rationalLevel) {flag : Flags .plane}
    (flag_good : GoodFlag .plane flag) : GoodFlag .plane (translate.val • flag) := by
  obtain ⟨integral, integral_eq⟩ := translate.property
  rw [← integral_eq]
  exact good_flag_arithmetic integral flag_good

theorem good_flag_level (translate : rationalLevel) (flag : Flags .plane) :
    GoodFlag .plane (translate.val • flag) ↔ GoodFlag .plane flag := by
  constructor
  · intro flag_good
    simpa only [Subgroup.coe_inv, inv_smul_smul] using
      good_flag_level_forward translate⁻¹ flag_good
  · exact good_flag_level_forward translate

def flagCut (keep_good : Bool) {degree : ℕ} {character : RankOneCharacter}
    (arity : ℕ) (cochain : MaximalCochains degree character .plane arity) :
    MaximalCochains degree character .plane arity :=
  ⟨fun coordinates flag =>
    if GoodFlag .plane flag then
      if keep_good then cochain.val coordinates flag else 0
    else if keep_good then 0 else cochain.val coordinates flag, by
    intro translate coordinates
    funext flag
    change (if GoodFlag .plane flag then
      if keep_good then cochain.val (fun index => translate.val * coordinates index) flag else 0
      else if keep_good then 0 else
        cochain.val (fun index => translate.val * coordinates index) flag) =
      rationalCoefficientComponent degree character translate.val
        (if GoodFlag .plane (translate.val⁻¹ • flag) then
          if keep_good then cochain.val coordinates (translate.val⁻¹ • flag) else 0
          else if keep_good then 0 else cochain.val coordinates (translate.val⁻¹ • flag))
    have invariance := good_flag_level translate⁻¹ flag
    rw [Subgroup.coe_inv] at invariance
    rw [invariance]
    have equivariance := congrFun (cochain.property translate coordinates) flag
    change cochain.val (fun index => translate.val * coordinates index) flag =
      rationalCoefficientComponent degree character translate.val
        (cochain.val coordinates (translate.val⁻¹ • flag)) at equivariance
    split_ifs <;> simp only [map_zero, equivariance]⟩

theorem flag_cut_differential_one {degree : ℕ} {character : RankOneCharacter}
    (keep_good : Bool) (cochain : MaximalCochains degree character .plane 1) :
    flagCut keep_good 2
        (differentialOne rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree character) .plane) cochain) =
      differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) .plane)
        (flagCut keep_good 1 cochain) := by
  apply Subtype.ext
  funext coordinates flag
  change (if GoodFlag .plane flag then
    if keep_good then cochain.val ![coordinates 1, coordinates 2] flag -
      cochain.val ![coordinates 0, coordinates 2] flag +
      cochain.val ![coordinates 0, coordinates 1] flag else 0
    else if keep_good then 0 else cochain.val ![coordinates 1, coordinates 2] flag -
      cochain.val ![coordinates 0, coordinates 2] flag +
      cochain.val ![coordinates 0, coordinates 1] flag) = _
  cases keep_good <;> by_cases flag_good : GoodFlag .plane flag <;>
    simp [flagCut, differentialOne, flag_good]

def flagCutCycle {degree : ℕ} {character : RankOneCharacter}
    (keep_good : Bool) (cycle : MaximalCycles degree character .plane) :
    MaximalCycles degree character .plane :=
  ⟨flagCut keep_good 2 cycle.val, by
    have cycle_closed := cycle.property
    change differentialTwo rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .plane) cycle.val = 0
      at cycle_closed
    change differentialTwo rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .plane)
      (flagCut keep_good 2 cycle.val) = 0
    funext coordinates flag
    have closed_value := congrFun (congrFun cycle_closed coordinates) flag
    cases keep_good <;> by_cases flag_good : GoodFlag .plane flag
    · simp [flagCut, differentialTwo, flag_good]
    · simpa [flagCut, differentialTwo, flag_good] using closed_value
    · simpa [flagCut, differentialTwo, flag_good] using closed_value
    · simp [flagCut, differentialTwo, flag_good]⟩

theorem bad_source_evaluates {degree : ℕ} {data : InducingData degree}
    {source : SourceCochain degree} {cycle : MaximalCycles degree data.chi .plane}
    (evaluation : Evaluates data .plane source cycle) :
    Evaluates data .plane (badSource source) (flagCutCycle false cycle) := by
  intro coordinates frame
  change (if GoodFlag .plane (QuotientGroup.mk frame) then 0 else
    cycle.val.val coordinates (QuotientGroup.mk frame)) =
    badSource source (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (coordinates index))
      (rationalGroup frame⁻¹)
  rw [evaluation coordinates frame]
  simp only [badSource, badCut, adelic_good_rational]

theorem cycle_vanishes_on_good {degree : ℕ} {character : RankOneCharacter}
    (cycle : MaximalCycles degree character .plane)
    (vanishing : VanishesOnGood degree character .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) .plane) cycle)) :
    ∃ cochain : MaximalCochains degree character .plane 1,
      ∀ coordinates flag, GoodFlag .plane flag →
        cycle.val.val coordinates flag =
          (differentialOne rationalLevel
            (flagRepresentation (rationalCoefficientComponent degree character) .plane)
            cochain).val coordinates flag := by
  obtain ⟨other_cycle, same_class, cochain, cochain_good⟩ := vanishing
  have boundary_membership : cycle - other_cycle ∈
      LinearMap.range (boundaryMap rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) .plane)) :=
    (Submodule.Quotient.eq _).mp same_class.symm
  obtain ⟨difference, difference_eq⟩ := LinearMap.mem_range.mp boundary_membership
  refine ⟨cochain + difference, ?_⟩
  intro coordinates flag flag_good
  have difference_value := congrArg
    (fun value : MaximalCycles degree character .plane => value.val.val coordinates flag)
    difference_eq
  change (differentialOne rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree character) .plane)
    difference).val coordinates flag =
    cycle.val.val coordinates flag - other_cycle.val.val coordinates flag at difference_value
  rw [map_add]
  change cycle.val.val coordinates flag =
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .plane)
      cochain).val coordinates flag +
    (differentialOne rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree character) .plane)
      difference).val coordinates flag
  rw [difference_value, ← cochain_good coordinates flag flag_good]
  abel

theorem bad_cut_same_class {degree : ℕ} {character : RankOneCharacter}
    (cycle : MaximalCycles degree character .plane)
    (vanishing : VanishesOnGood degree character .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) .plane) cycle)) :
    classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) .plane)
        (flagCutCycle false cycle) =
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree character) .plane) cycle := by
  obtain ⟨cochain, cochain_good⟩ := cycle_vanishes_on_good cycle vanishing
  apply (Submodule.Quotient.eq _).mpr
  apply LinearMap.mem_range.mpr
  refine ⟨-(flagCut true 1 cochain), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext coordinates flag
  change -(if GoodFlag .plane flag then cochain.val ![coordinates 1, coordinates 2] flag else 0) -
    -(if GoodFlag .plane flag then cochain.val ![coordinates 0, coordinates 2] flag else 0) +
    -(if GoodFlag .plane flag then cochain.val ![coordinates 0, coordinates 1] flag else 0) =
    (if GoodFlag .plane flag then 0 else cycle.val.val coordinates flag) -
      cycle.val.val coordinates flag
  by_cases flag_good : GoodFlag .plane flag
  · simp only [ite_eq_left flag_good]
    rw [cochain_good coordinates flag flag_good]
    change -cochain.val ![coordinates 1, coordinates 2] flag -
      -cochain.val ![coordinates 0, coordinates 2] flag +
      -cochain.val ![coordinates 0, coordinates 1] flag =
      0 - (cochain.val ![coordinates 1, coordinates 2] flag -
        cochain.val ![coordinates 0, coordinates 2] flag +
        cochain.val ![coordinates 0, coordinates 1] flag)
    abel
  · simp only [ite_eq_right flag_good, neg_zero, sub_self, add_zero]

end

end TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers
