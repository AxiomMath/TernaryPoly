module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeEndpoints
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeComparison

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRelative_extremal_of_upper_lift (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL) (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_mem : ∀ position, lower position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree (-2) position))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper)
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0)
    (nontrivial : ¬∃ primitive : binarySmoothValues cusp (Fin (degree + 2)),
      (∀ element : level, ∀ position, cusp.π (atFinite element.val) (primitive position).val = (primitive position).val) ∧
      (∀ angle : Circle, binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) (binaryRotations angle)
        (binarySmoothValues_val cusp primitive) = binarySmoothValues_val cusp primitive) ∧
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0 primitive = lower ∧
      binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) 0 primitive = upper)
    (boundary : cuspAffineSmoothValues cusp)
    (boundary_mem : boundary ∈ cuspFiniteWeightValues cusp level (degree + 1 : ℕ))
    (boundary_raising : cuspRaisingOperator cusp (degree + 1 : ℕ) boundary = upper (Fin.last (degree + 1))) :
    ∃ vector : cuspAffineSmoothValues cusp, vector ≠ 0 ∧
      vector ∈ cuspFiniteWeightValues cusp level (-2 - (degree + 1 : ℕ)) ∧
      cuspRaisingOperator cusp (-2 - (degree + 1 : ℕ)) vector = 0 := by
  let basis := binaryWeightBasis (degree + 1)
  obtain ⟨primitive, last_value, primitive_mem, primitive_support⟩ :=
    binaryRelativeLowering_lift_boundary cusp degree level boundary boundary_mem
  let new_lower := lower - binaryRelativeLowering cusp basis 0 primitive
  let new_upper := upper - binaryRelativeRaising cusp basis 0 primitive
  have new_closed := binaryRelativeLadder_shift cusp basis lower upper primitive closed
  have new_support (position : Fin (degree + 1)) : new_lower position.succ = 0 := by
    change lower position.succ - binaryRelativeLowering cusp basis 0 primitive position.succ = 0
    rw [support, primitive_support, sub_self]
  have endpoint_zero : new_upper (Fin.last (degree + 1)) = 0 := by
    change upper (Fin.last (degree + 1)) - binaryRelativeRaising cusp basis 0 primitive (Fin.last (degree + 1)) = 0
    rw [binaryRelativeRaising_last, zero_add, last_value, boundary_raising, sub_self]
  have upper_zero : new_upper = 0 :=
    binaryRelative_normal_form_upper_zero cusp degree new_lower new_upper new_closed new_support endpoint_zero
  have lower_nonzero : new_lower 0 ≠ 0 := by
    intro endpoint_zero
    have lower_zero : new_lower = 0 := by
      funext position
      exact Fin.cases endpoint_zero new_support position
    apply nontrivial
    refine ⟨primitive, fun element position => (primitive_mem position).1 element, ?_, ?_, ?_⟩
    · intro angle
      simpa only [zpow_zero, one_smul] using
        binaryFiniteWeightValues_rotation cusp degree level 0 primitive primitive_mem angle
    · exact (sub_eq_zero.mp lower_zero).symm
    · exact (sub_eq_zero.mp upper_zero).symm
  have vector_mem : new_lower 0 ∈ cuspFiniteWeightValues cusp level (-2 - (degree + 1 : ℕ)) := by
    have member := Submodule.sub_mem _ (lower_mem 0)
      (binaryRelativeLowering_mem cusp degree level 0 primitive primitive_mem 0)
    simpa only [new_lower, basis, Pi.sub_apply, binaryUnitaryWeight, Fin.val_zero,
      Nat.cast_zero, mul_zero, add_zero] using member
  refine ⟨new_lower 0, lower_nonzero, vector_mem, ?_⟩
  have equation := (binaryRelative_normal_form_equations cusp degree new_lower new_upper new_closed new_support).1
  rw [upper_zero, Pi.zero_apply, map_zero] at equation
  exact equation

theorem cohomological_extremal_or_raising_obstruction (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ∃ level : Subgroup BinaryFiniteGL,
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      ((∃ vector : cuspAffineSmoothValues cusp, vector ≠ 0 ∧
          vector ∈ cuspFiniteWeightValues cusp level (-2 - (degree + 1 : ℕ)) ∧
          cuspRaisingOperator cusp (-2 - (degree + 1 : ℕ)) vector = 0) ∨
        ∃ vector : cuspAffineSmoothValues cusp,
          vector ∈ cuspFiniteWeightValues cusp level (2 + (degree + 1 : ℕ)) ∧
          ¬∃ preimage : cuspAffineSmoothValues cusp,
            preimage ∈ cuspFiniteWeightValues cusp level (degree + 1 : ℕ) ∧
            cuspRaisingOperator cusp (degree + 1 : ℕ) preimage = vector) := by
  obtain ⟨level, cycle, lower, upper, level_open, level_compact, nonzero, regular, rotations_zero,
    _, lower_mem, upper_mem, lower_value, upper_value, closed, support, _⟩ :=
    cohomological_exists_relative_normal_form cusp spherical cohomological
  refine ⟨level, level_open, level_compact, ?_⟩
  by_cases lifts : ∃ preimage : cuspAffineSmoothValues cusp,
      preimage ∈ cuspFiniteWeightValues cusp level (degree + 1 : ℕ) ∧
      cuspRaisingOperator cusp (degree + 1 : ℕ) preimage = upper (Fin.last (degree + 1))
  · obtain ⟨preimage, preimage_mem, preimage_raising⟩ := lifts
    left
    apply binaryRelative_extremal_of_upper_lift cusp degree level lower upper lower_mem closed support _
      preimage preimage_mem preimage_raising
    exact mt (binaryRelativePair_coboundary_iff cusp spherical cohomological (binaryWeightBasis (degree + 1))
      level level_open level_compact cycle regular rotations_zero lower upper lower_value upper_value).mpr nonzero
  · right
    refine ⟨upper (Fin.last (degree + 1)), ?_, lifts⟩
    have weight : binaryUnitaryWeight degree 2 (Fin.last (degree + 1)) = 2 + (degree + 1 : ℕ) := by
      simp only [binaryUnitaryWeight, Fin.val_last]
      omega
    rw [← weight]
    exact upper_mem _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
