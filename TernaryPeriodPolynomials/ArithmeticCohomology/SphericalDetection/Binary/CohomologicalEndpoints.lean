module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CohomologicalWeightGap
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointFiniteResidual

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRelativeBoundaryLift_zero (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL) : binaryRelativeBoundaryLift cusp degree level 0 = 0 := by
  apply binaryRelativeBoundaryLift_eq cusp degree level 0 0 rfl
  intro position
  rw [map_zero]
  rfl

theorem binaryEndpointBoundary_iff_zero (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL) (lower upper : cuspAffineSmoothValues cusp) :
    (∃ boundary : cuspFiniteWeightValues cusp level (degree + 1 : ℕ),
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0
        (binaryRelativeBoundaryLift cusp degree level boundary) 0 = lower ∧
      cuspRaisingOperator cusp (degree + 1 : ℕ) boundary.val = upper) ↔ lower = 0 ∧ upper = 0 := by
  constructor
  · rintro ⟨boundary, lower_eq, upper_eq⟩
    rw [cohomological_boundary_weight_zero cusp spherical odd cohomological level boundary,
      binaryRelativeBoundaryLift_zero, map_zero] at lower_eq
    rw [cohomological_boundary_weight_zero cusp spherical odd cohomological level boundary] at upper_eq
    simp only [Submodule.coe_zero, map_zero] at upper_eq
    exact ⟨lower_eq.symm, upper_eq.symm⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨0, ?_, map_zero _⟩
    rw [binaryRelativeBoundaryLift_zero, map_zero]
    rfl

theorem binaryRelative_weight_gap_support (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL) (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_mem : ∀ position, lower position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree (-2) position))
    (upper_mem : ∀ position, upper position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 2 position)) :
    (∀ position : Fin (degree + 1), lower position.succ = 0) ∧
      (∀ position : Fin (degree + 1), upper position.castSucc = 0) := by
  constructor
  · intro position
    apply Subtype.ext
    apply cohomological_cusp_weight_gap cusp spherical odd cohomological _ _ _ _ (lower_mem position.succ).2
    · simp only [binaryUnitaryWeight, Fin.val_succ]; omega
    · simp only [binaryUnitaryWeight, Fin.val_succ]; omega
  · intro position
    apply Subtype.ext
    apply cohomological_cusp_weight_gap cusp spherical odd cohomological _ _ _ _ (upper_mem position.castSucc).2
    · simp only [binaryUnitaryWeight, Fin.val_castSucc]; omega
    · simp only [binaryUnitaryWeight, Fin.val_castSucc]; omega

theorem binaryRelative_endpoint_kernels (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL) (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_mem : ∀ position, lower position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree (-2) position))
    (upper_mem : ∀ position, upper position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 2 position))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper) :
    cuspRaisingOperator cusp (-((degree : ℤ) + 3)) (lower 0) = 0 ∧
      cuspLoweringOperator cusp ((degree : ℤ) + 3) (upper (Fin.last (degree + 1))) = 0 := by
  obtain ⟨lower_support, upper_support⟩ := binaryRelative_weight_gap_support cusp spherical odd cohomological
    level lower upper lower_mem upper_mem
  obtain ⟨first, rest⟩ := binaryRelative_normal_form_equations cusp degree lower upper closed lower_support
  have upper_first : upper 0 = 0 := upper_support 0
  have first_weight : -2 - ((degree + 1 : ℕ) : ℤ) = -((degree : ℤ) + 3) := by omega
  rw [upper_first, map_zero, first_weight] at first
  refine ⟨first, ?_⟩
  have last := rest (Fin.last degree)
  rw [upper_support, smul_zero, zero_add] at last
  have last_weight : binaryUnitaryWeight degree 2 (Fin.last degree).succ = (degree : ℤ) + 3 := by
    simp only [binaryUnitaryWeight, Fin.val_succ, Fin.val_last]
    omega
  rw [last_weight] at last
  exact last

end TernaryPeriodPolynomials.SphericalDetection.Helpers
