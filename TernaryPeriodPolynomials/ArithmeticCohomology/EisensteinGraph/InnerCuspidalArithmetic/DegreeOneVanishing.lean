module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LowDegreeParabolic

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.DegreeOneVanishing

open Helpers ArithmeticGenerators LowDegreeParabolic

theorem upper_negative_one : upper (-1) = (upper 1)⁻¹ := by
  rw [upper_zpow]
  simp

theorem upper_reflection : upper 1 * reflection = reflection * upper (-1) := by
  apply Subtype.ext
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [upper, reflection, Matrix.mul_apply, Fin.sum_univ_two]

theorem reflection_square : reflection * reflection = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [reflection, Matrix.mul_apply, Fin.sum_univ_two]

theorem reflection_cocycle_zero
    (cycle : crossedCocycles (binaryArithmeticRepresentation 1))
    (upperZero : cycle.val (upper 1) = 0) : cycle.val reflection = 0 := by
  have inverseZero : cycle.val (upper (-1)) = 0 := by
    rw [upper_negative_one]
    exact (crossedCocycleZeroSubgroup _ cycle).inv_mem upperZero
  have first := cycle.property (upper 1) reflection
  have second := cycle.property reflection (upper (-1))
  rw [upper_reflection, upperZero, zero_add] at first
  rw [inverseZero, map_zero, add_zero] at second
  have fixed : binaryArithmeticRepresentation 1 (upper 1) (cycle.val reflection) =
      cycle.val reflection := first.symm.trans second
  have square := cycle.property reflection reflection
  rw [reflection_square, crossedCocycle_one] at square
  have negative : binaryArithmeticRepresentation 1 reflection (cycle.val reflection) =
      -cycle.val reflection := by
    exact eq_neg_of_add_eq_zero_right square.symm
  exact quadratic_upper_reflection_zero _ fixed negative

def secondSquare (scalar : ℂ) : Binary.HomogeneousPoly 2 :=
  ⟨C scalar * X 1 ^ 2, (isHomogeneous_C (Fin 2) scalar).mul (isHomogeneous_X_pow 1 2)⟩

theorem secondSquare_action (matrix : binaryArithmeticLevel) (scalar : ℂ) :
    (binaryArithmeticRepresentation 1 matrix (secondSquare scalar)).val =
      C scalar * (C (matrix.val.inv 1 0 : ℂ) * X 0 +
        C (matrix.val.inv 1 1 : ℂ) * X 1) ^ 2 := by
  have first : Finsupp.single (1 : Fin 2) 2 ≠ Finsupp.single 0 2 := by
    intro equality
    have coordinate := congrArg (fun value : Fin 2 →₀ ℕ => value 0) equality
    norm_num at coordinate
  have second : Finsupp.single (1 : Fin 2) 2 ≠
      Finsupp.single 0 1 + Finsupp.single 1 1 := by
    intro equality
    have coordinate := congrArg (fun value : Fin 2 →₀ ℕ => value 0) equality
    norm_num at coordinate
  rw [quadratic_action]
  simp [secondSquare, exponent, X, monomial_pow, first, second]

theorem secondSquare_lower (scalar : ℂ) :
    (binaryArithmeticRepresentation 1 (lower (-1)) (secondSquare scalar)).val -
      (secondSquare scalar).val =
        C (9 * scalar) * X 0 ^ 2 + C (6 * scalar) * (X 0 * X 1) := by
  rw [secondSquare_action]
  norm_num [lower, secondSquare]
  simp only [map_ofNat]
  ring

theorem secondSquare_upper (scalar : ℂ) :
    binaryArithmeticRepresentation 1 (upper 1) (secondSquare scalar) = secondSquare scalar := by
  apply Subtype.ext
  rw [secondSquare_action]
  simp [upper, secondSquare]

theorem secondSquare_reflection (scalar : ℂ) :
    binaryArithmeticRepresentation 1 reflection (secondSquare scalar) = secondSquare scalar := by
  apply Subtype.ext
  rw [secondSquare_action]
  simp [reflection, secondSquare]

theorem lower_primitive
    (cycle : crossedCocycles (binaryArithmeticRepresentation 1))
    (upperZero : cycle.val (upper 1) = 0)
    (parabolic : (crossedBoundaries (binaryArithmeticRepresentation 1)).mkQ cycle ∈
      binaryParabolicH1 1) :
    cycle.val (lower (-1)) =
      binaryArithmeticRepresentation 1 (lower (-1))
        (secondSquare ((cycle.val (lower (-1))).val.coeff (exponent 1 1) / 6)) -
      secondSquare ((cycle.val (lower (-1))).val.coeff (exponent 1 1) / 6) := by
  obtain ⟨trailing, relation⟩ := lower_cocycle_quadratic_relation cycle upperZero parabolic
  apply Subtype.ext
  change (cycle.val (lower (-1))).val = _ - _
  rw [secondSquare_lower]
  conv_lhs => rw [quadratic_expansion]
  have coefficient : (cycle.val (lower (-1))).val.coeff (exponent 2 0) =
      9 * ((cycle.val (lower (-1))).val.coeff (exponent 1 1) / 6) := by
    linear_combination (1 / 2 : ℂ) * relation
  rw [coefficient, trailing]
  have middle : (cycle.val (lower (-1))).val.coeff (exponent 1 1) =
      6 * ((cycle.val (lower (-1))).val.coeff (exponent 1 1) / 6) := by ring
  change _ = C (9 * ((cycle.val (lower (-1))).val.coeff (exponent 1 1) / 6)) * X 0 ^ 2 +
    C (6 * ((cycle.val (lower (-1))).val.coeff (exponent 1 1) / 6)) * (X 0 * X 1)
  conv_lhs => rw [middle]
  simp

private theorem boundary_of_normalized {GroupType Value : Type} [Group GroupType]
    [AddCommGroup Value] [Module ℂ Value] (representation : Representation ℂ GroupType Value)
    (inner : Submodule ℂ (CrossedH1 representation)) (generator : GroupType)
    (primitiveExists : ∀ cycle : crossedCocycles representation,
      (crossedBoundaries representation).mkQ cycle ∈ inner →
        ∃ primitive : Value, cycle.val generator = representation generator primitive - primitive)
    (normalizedBoundary : ∀ cycle : crossedCocycles representation, cycle.val generator = 0 →
      (crossedBoundaries representation).mkQ cycle ∈ inner → cycle ∈ crossedBoundaries representation)
    (cycle : crossedCocycles representation)
    (parabolic : (crossedBoundaries representation).mkQ cycle ∈ inner) :
    cycle ∈ crossedBoundaries representation := by
  obtain ⟨primitive, formula⟩ := primitiveExists cycle parabolic
  let normalized := cycle - crossedBoundary representation primitive
  have generatorZero : normalized.val generator = 0 := by
    change cycle.val generator - (representation generator primitive - primitive) = 0
    rw [formula, sub_self]
  have primitiveZero : (crossedBoundaries representation).mkQ
      (crossedBoundary representation primitive) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨primitive, rfl⟩
  have normalizedClass : (crossedBoundaries representation).mkQ normalized =
      (crossedBoundaries representation).mkQ cycle := by
    change (crossedBoundaries representation).mkQ
      (cycle - crossedBoundary representation primitive) = _
    rw [map_sub, primitiveZero, sub_zero]
  have belongs := normalizedBoundary normalized generatorZero (normalizedClass ▸ parabolic)
  have boundaryBelongs : crossedBoundary representation primitive ∈ crossedBoundaries representation :=
    ⟨primitive, rfl⟩
  have equality : cycle = normalized + crossedBoundary representation primitive := by
    exact (sub_add_cancel _ _).symm
  rw [equality]
  exact (crossedBoundaries representation).add_mem belongs boundaryBelongs

theorem cocycle_zero_of_generators {degree : ℕ}
    (cycle : crossedCocycles (binaryArithmeticRepresentation degree))
    (upperZero : cycle.val (upper 1) = 0) (lowerZero : cycle.val (lower (-1)) = 0)
    (reflectionZero : cycle.val reflection = 0) : cycle = 0 := by
  let zeroSubgroup := crossedCocycleZeroSubgroup _ cycle
  have negativeLower : lower (-1) = (lower 1)⁻¹ := by
    rw [lower_zpow]
    simp
  have positiveLower : lower 1 ∈ zeroSubgroup := by
    have inverse := zeroSubgroup.inv_mem lowerZero
    simpa only [negativeLower, inv_inv] using inverse
  have contains : generated ≤ zeroSubgroup := by
    apply (Subgroup.closure_le _).mpr
    intro element membership
    rcases Set.mem_insert_iff.mp membership with first | rest
    · subst element
      exact upperZero
    · rcases Set.mem_insert_iff.mp rest with second | third
      · subst element
        exact positiveLower
      · have equality := Set.mem_singleton_iff.mp third
        subst element
        exact reflectionZero
  apply Subtype.ext
  funext element
  exact contains (by rw [generators_span]; exact Subgroup.mem_top element)

theorem normalized_parabolic_cocycle_boundary
    (cycle : crossedCocycles (binaryArithmeticRepresentation 1))
    (upperZero : cycle.val (upper 1) = 0)
    (parabolic : (crossedBoundaries (binaryArithmeticRepresentation 1)).mkQ cycle ∈
      binaryParabolicH1 1) : cycle ∈ crossedBoundaries (binaryArithmeticRepresentation 1) := by
  let correction := secondSquare ((cycle.val (lower (-1))).val.coeff (exponent 1 1) / 6)
  let finalCycle := cycle - crossedBoundary (binaryArithmeticRepresentation 1) correction
  have finalUpper : finalCycle.val (upper 1) = 0 := by
    change cycle.val (upper 1) -
      (binaryArithmeticRepresentation 1 (upper 1) correction - correction) = 0
    rw [upperZero, secondSquare_upper, sub_self, sub_self]
  have finalLower : finalCycle.val (lower (-1)) = 0 := by
    change cycle.val (lower (-1)) -
      (binaryArithmeticRepresentation 1 (lower (-1)) correction - correction) = 0
    rw [lower_primitive cycle upperZero parabolic]
    exact sub_self _
  have finalReflection : finalCycle.val reflection = 0 := by
    change cycle.val reflection -
      (binaryArithmeticRepresentation 1 reflection correction - correction) = 0
    rw [reflection_cocycle_zero cycle upperZero, secondSquare_reflection, sub_self, sub_self]
  have finalZero := cocycle_zero_of_generators finalCycle finalUpper finalLower finalReflection
  have normalizedBoundary : cycle = crossedBoundary (binaryArithmeticRepresentation 1) correction :=
    sub_eq_zero.mp finalZero
  exact ⟨correction, normalizedBoundary.symm⟩

theorem parabolic_cocycle_boundary
    (cycle : crossedCocycles (binaryArithmeticRepresentation 1))
    (parabolic : (crossedBoundaries (binaryArithmeticRepresentation 1)).mkQ cycle ∈
      binaryParabolicH1 1) : cycle ∈ crossedBoundaries (binaryArithmeticRepresentation 1) :=
  boundary_of_normalized (binaryArithmeticRepresentation 1) (binaryParabolicH1 1) (upper 1)
    (fun cycle membership => parabolic_generator_primitive cycle membership 1 (upper 1) upper_cusp)
    normalized_parabolic_cocycle_boundary cycle parabolic

private theorem quotient_submodule_eq_bot {Value : Type} [AddCommGroup Value] [Module ℂ Value]
    (boundaries : Submodule ℂ Value) (inner : Submodule ℂ (Value ⧸ boundaries))
    (vanishing : ∀ cycle : Value, boundaries.mkQ cycle ∈ inner → cycle ∈ boundaries) :
    inner = ⊥ := by
  apply le_antisymm
  · intro coordinate membership
    obtain ⟨cycle, rfl⟩ := boundaries.mkQ_surjective coordinate
    exact (Submodule.Quotient.mk_eq_zero _).mpr (vanishing cycle membership)
  · exact bot_le

private theorem crossed_submodule_eq_bot {GroupType Value : Type} [Group GroupType]
    [AddCommGroup Value] [Module ℂ Value] (representation : Representation ℂ GroupType Value)
    (inner : Submodule ℂ (CrossedH1 representation))
    (vanishing : ∀ cycle : crossedCocycles representation,
      (crossedBoundaries representation).mkQ cycle ∈ inner → cycle ∈ crossedBoundaries representation) :
    inner = ⊥ := quotient_submodule_eq_bot (crossedBoundaries representation) inner vanishing

theorem binaryParabolicH1_degree_one_eq_bot : binaryParabolicH1 1 = ⊥ :=
  crossed_submodule_eq_bot (binaryArithmeticRepresentation 1) (binaryParabolicH1 1)
    parabolic_cocycle_boundary

theorem innerBadLineClasses_degree_one_eq_bot : innerBadLineClasses 1 = ⊥ := by
  apply le_antisymm
  · intro coordinate membership
    let innerClass : innerBadLineClasses 1 := ⟨coordinate, membership⟩
    have mappedZero : innerBadLineParabolicMap 1 (by omega) innerClass = 0 := by
      apply Subtype.ext
      exact (Submodule.mem_bot ℂ).mp (binaryParabolicH1_degree_one_eq_bot ▸
        (innerBadLineParabolicMap 1 (by omega) innerClass).property)
    have zero := (innerBadLineParabolicMap_zero_iff 1 (by omega) innerClass).mp mappedZero
    exact congrArg Subtype.val zero
  · exact bot_le

theorem inner_bad_line_degree_one_zero (coordinate : StratumH2 1 trivialCharacter .line)
    (good : VanishesOnGood 1 trivialCharacter .line coordinate)
    (inner : InnerBoundary 1 trivialCharacter .line coordinate) : coordinate = 0 := by
  have membership := (mem_innerBadLineClasses_iff 1 coordinate).mpr ⟨good, inner⟩
  rw [innerBadLineClasses_degree_one_eq_bot] at membership
  exact membership

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.DegreeOneVanishing
