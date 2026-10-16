module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.DegreeOneVanishing

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.DegreeTwoVanishing

open Helpers ArithmeticGenerators LowDegreeParabolic DegreeOneVanishing

theorem cubic_expansion (polynomial : Binary.HomogeneousPoly 3) :
    polynomial.val = C (polynomial.val.coeff (exponent 3 0)) * X 0 ^ 3 +
      C (polynomial.val.coeff (exponent 2 1)) * (X 0 ^ 2 * X 1) +
      C (polynomial.val.coeff (exponent 1 2)) * (X 0 * X 1 ^ 2) +
      C (polynomial.val.coeff (exponent 0 3)) * X 1 ^ 3 := by
  have different : ∀ first second : Fin 4, first ≠ second →
      exponent first.val (3 - first.val) ≠ exponent second.val (3 - second.val) := by
    intro first second inequality equality
    apply inequality
    apply Fin.ext
    have coordinate := congrArg (fun value : Fin 2 →₀ ℕ => value 0) equality
    simpa [exponent] using coordinate
  apply MvPolynomial.ext
  intro monomialIndex
  by_cases degree : Finsupp.degree monomialIndex = 3
  · have coordinates : monomialIndex 0 + monomialIndex 1 = 3 := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using degree
    have cases : monomialIndex = exponent 3 0 ∨ monomialIndex = exponent 2 1 ∨
        monomialIndex = exponent 1 2 ∨ monomialIndex = exponent 0 3 := by
      by_cases first : monomialIndex 0 = 3
      · left
        ext index
        fin_cases index <;> simp [exponent, first, show monomialIndex 1 = 0 by omega]
      · by_cases second : monomialIndex 0 = 2
        · right
          left
          ext index
          fin_cases index <;> simp [exponent, second, show monomialIndex 1 = 1 by omega]
        · by_cases third : monomialIndex 0 = 1
          · right
            right
            left
            ext index
            fin_cases index <;> simp [exponent, third, show monomialIndex 1 = 2 by omega]
          · right
            right
            right
            ext index
            fin_cases index <;> simp [exponent, show monomialIndex 0 = 0 by omega,
              show monomialIndex 1 = 3 by omega]
    have separated : exponent 3 0 ≠ exponent 2 1 ∧ exponent 3 0 ≠ exponent 1 2 ∧
        exponent 3 0 ≠ exponent 0 3 ∧ exponent 2 1 ≠ exponent 1 2 ∧
        exponent 2 1 ≠ exponent 0 3 ∧ exponent 1 2 ≠ exponent 0 3 := by
      exact ⟨different 3 2 (by decide), different 3 1 (by decide), different 3 0 (by decide),
        different 2 1 (by decide), different 2 0 (by decide), different 1 0 (by decide)⟩
    simp only [exponent, Finsupp.single_zero, zero_add, add_zero] at separated
    rcases cases with first | second | third | fourth
    all_goals subst monomialIndex
    all_goals simp [X, monomial_pow, coeff_monomial, separated.1, separated.2.1,
      separated.2.2.1, separated.2.2.2.1, separated.2.2.2.2.1, separated.2.2.2.2.2,
      Ne.symm separated.1, Ne.symm separated.2.1, Ne.symm separated.2.2.1,
      Ne.symm separated.2.2.2.1, Ne.symm separated.2.2.2.2.1, Ne.symm separated.2.2.2.2.2,
      exponent]
  · have coefficientZero : polynomial.val.coeff monomialIndex = 0 := by
      rw [← homogeneousComponent_eq_self polynomial.property]
      simp [coeff_homogeneousComponent, degree]
    have outside : ∀ first : Fin 4, exponent first.val (3 - first.val) ≠ monomialIndex := by
      intro first equality
      apply degree
      rw [← equality]
      fin_cases first <;> simp [exponent]
    rw [coefficientZero]
    have first : exponent 3 0 ≠ monomialIndex := outside 3
    have second : exponent 2 1 ≠ monomialIndex := outside 2
    have third : exponent 1 2 ≠ monomialIndex := outside 1
    have fourth : exponent 0 3 ≠ monomialIndex := outside 0
    simp only [exponent, Finsupp.single_zero, zero_add, add_zero] at first fourth
    change Finsupp.single 0 2 + Finsupp.single 1 1 ≠ monomialIndex at second
    change Finsupp.single 0 1 + Finsupp.single 1 2 ≠ monomialIndex at third
    simp [X, monomial_pow, exponent, first, second, third, fourth]

theorem cubic_action (matrix : binaryArithmeticLevel) (polynomial : Binary.HomogeneousPoly 3) :
    (binaryArithmeticRepresentation 2 matrix polynomial).val =
      C (polynomial.val.coeff (exponent 3 0)) *
        (C (matrix.val.inv 0 0 : ℂ) * X 0 + C (matrix.val.inv 0 1 : ℂ) * X 1) ^ 3 +
      C (polynomial.val.coeff (exponent 2 1)) *
        ((C (matrix.val.inv 0 0 : ℂ) * X 0 + C (matrix.val.inv 0 1 : ℂ) * X 1) ^ 2 *
          (C (matrix.val.inv 1 0 : ℂ) * X 0 + C (matrix.val.inv 1 1 : ℂ) * X 1)) +
      C (polynomial.val.coeff (exponent 1 2)) *
        ((C (matrix.val.inv 0 0 : ℂ) * X 0 + C (matrix.val.inv 0 1 : ℂ) * X 1) *
          (C (matrix.val.inv 1 0 : ℂ) * X 0 + C (matrix.val.inv 1 1 : ℂ) * X 1) ^ 2) +
      C (polynomial.val.coeff (exponent 0 3)) *
        (C (matrix.val.inv 1 0 : ℂ) * X 0 + C (matrix.val.inv 1 1 : ℂ) * X 1) ^ 3 := by
  change Binary.action 0 (binaryIntegralComplex matrix.val) polynomial.val = _
  rw [Binary.action_apply]
  change (1 : ℂ) • Binary.substitute (binaryIntegralComplex matrix.val)⁻¹.val polynomial.val = _
  rw [one_smul]
  have inverse : (binaryIntegralComplex matrix.val)⁻¹ = binaryIntegralComplex matrix.val⁻¹ :=
    (map_inv binaryIntegralComplex matrix.val).symm
  have entries : ∀ row column, ((binaryIntegralComplex matrix.val)⁻¹).val row column =
      (matrix.val.inv row column : ℂ) := by
    intro row column
    rw [inverse]
    rfl
  have constants : ∀ coefficient : ℂ,
      Binary.substitute ((binaryIntegralComplex matrix.val)⁻¹).val (C coefficient) = C coefficient := by
    intro coefficient
    simp [Binary.substitute]
  conv_lhs => rw [cubic_expansion]
  simp only [map_add, map_mul, map_pow, constants, Binary.substitute_X,
    Binary.linearForm, Fin.sum_univ_two, entries]

theorem cubic_coefficients_zero (polynomial : Binary.HomogeneousPoly 3)
    (first : polynomial.val.coeff (exponent 3 0) = 0)
    (second : polynomial.val.coeff (exponent 2 1) = 0)
    (third : polynomial.val.coeff (exponent 1 2) = 0)
    (fourth : polynomial.val.coeff (exponent 0 3) = 0) : polynomial = 0 := by
  apply Subtype.ext
  rw [cubic_expansion, first, second, third, fourth]
  simp

theorem cubic_upper_reflection_zero (polynomial : Binary.HomogeneousPoly 3)
    (upperFixed : binaryArithmeticRepresentation 2 (upper 1) polynomial = polynomial)
    (reflectionNeg : binaryArithmeticRepresentation 2 reflection polynomial = -polynomial) :
    polynomial = 0 := by
  have upperEquation := congrArg Subtype.val upperFixed
  have reflectionEquation := congrArg Subtype.val reflectionNeg
  rw [cubic_action] at upperEquation reflectionEquation
  have first := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → ℂ)) upperEquation
  have second := congrArg (MvPolynomial.eval (![1, 1] : Fin 2 → ℂ)) upperEquation
  have third := congrArg (MvPolynomial.eval (![-1, 1] : Fin 2 → ℂ)) upperEquation
  have fourth := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → ℂ)) reflectionEquation
  conv_rhs at first => rw [cubic_expansion]
  conv_rhs at second => rw [cubic_expansion]
  conv_rhs at third => rw [cubic_expansion]
  change _ = MvPolynomial.eval (![0, 1] : Fin 2 → ℂ) (-polynomial.val) at fourth
  conv_rhs at fourth => rw [cubic_expansion]
  norm_num [upper, reflection] at first second third fourth
  apply cubic_coefficients_zero polynomial
  · linear_combination (1 / 3 : ℂ) * first + (1 / 6 : ℂ) * second - (1 / 6 : ℂ) * third
  · linear_combination (1 / 2 : ℂ) * first + (1 / 2 : ℂ) * second
  · linear_combination - (5 / 6 : ℂ) * first + (1 / 3 : ℂ) * second + (1 / 6 : ℂ) * third
  · linear_combination (1 / 2 : ℂ) * fourth

theorem reflection_cocycle_zero
    (cycle : crossedCocycles (binaryArithmeticRepresentation 2))
    (upperZero : cycle.val (upper 1) = 0) : cycle.val reflection = 0 := by
  have inverseZero : cycle.val (upper (-1)) = 0 := by
    rw [upper_negative_one]
    exact (crossedCocycleZeroSubgroup _ cycle).inv_mem upperZero
  have first := cycle.property (upper 1) reflection
  have second := cycle.property reflection (upper (-1))
  rw [upper_reflection, upperZero, zero_add] at first
  rw [inverseZero, map_zero, add_zero] at second
  have fixed : binaryArithmeticRepresentation 2 (upper 1) (cycle.val reflection) =
      cycle.val reflection := first.symm.trans second
  have square := cycle.property reflection reflection
  rw [reflection_square, crossedCocycle_one] at square
  exact cubic_upper_reflection_zero _ fixed (eq_neg_of_add_eq_zero_right square.symm)

private theorem cubic_eval_zero_one (polynomial : Binary.HomogeneousPoly 3) :
    MvPolynomial.eval (![0, 1] : Fin 2 → ℂ) polynomial.val =
      polynomial.val.coeff (exponent 0 3) := by
  conv_lhs => rw [cubic_expansion]
  simp only [map_add, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]
  norm_num

theorem lower_cocycle_cubic_relation
    (cycle : crossedCocycles (binaryArithmeticRepresentation 2))
    (upperZero : cycle.val (upper 1) = 0)
    (parabolic : (crossedBoundaries (binaryArithmeticRepresentation 2)).mkQ cycle ∈
      binaryParabolicH1 2) :
    (cycle.val (lower (-1))).val.coeff (exponent 0 3) = 0 ∧
      (cycle.val (lower (-1))).val.coeff (exponent 2 1) =
        3 * (cycle.val (lower (-1))).val.coeff (exponent 1 2) ∧
      (cycle.val (lower (-1))).val.coeff (exponent 3 0) =
        3 * (cycle.val (lower (-1))).val.coeff (exponent 1 2) := by
  obtain ⟨primitive, primitiveFormula⟩ := parabolic_generator_primitive cycle parabolic oppositeFrame
    (lower (-1)) lower_cusp
  have trailing := congrArg (fun value : Binary.HomogeneousPoly 3 =>
    MvPolynomial.eval (![0, 1] : Fin 2 → ℂ) value.val) primitiveFormula
  simp only [Submodule.coe_sub, map_sub] at trailing
  rw [cubic_eval_zero_one, cubic_action, cubic_eval_zero_one] at trailing
  norm_num [lower] at trailing
  have trailingZero : (cycle.val (lower (-1))).val.coeff (exponent 0 3) = 0 := by
    simpa [lower] using trailing
  have ellipticValue := cycle.property (upper 1) (lower (-1))
  rw [upperZero, zero_add] at ellipticValue
  have normZero := cocycle_cube (binaryArithmeticRepresentation 2) cycle _ elliptic_cube
  rw [ellipticValue] at normZero
  have first := congrArg (fun value : Binary.HomogeneousPoly 3 =>
    MvPolynomial.eval (![0, 1] : Fin 2 → ℂ) value.val) normZero
  have second := congrArg (fun value : Binary.HomogeneousPoly 3 =>
    MvPolynomial.eval (![1, 0] : Fin 2 → ℂ) value.val) normZero
  have actionProduct (matrix : binaryArithmeticLevel) (polynomial : Binary.HomogeneousPoly 3) :
      binaryArithmeticRepresentation 2 matrix
        (binaryArithmeticRepresentation 2 (upper 1) polynomial) =
      binaryArithmeticRepresentation 2 (matrix * upper 1) polynomial := by
    rw [map_mul, Module.End.mul_apply]
  simp only [Submodule.coe_add, Submodule.coe_zero, map_add, map_zero] at first second
  rw [cubic_action, actionProduct, actionProduct, cubic_action, cubic_action] at first second
  norm_num [upper, lower, pow_two, Matrix.mul_apply, Fin.sum_univ_two] at first second
  have firstNormalized : -(cycle.val (lower (-1))).val.coeff (exponent 2 1) +
      3 * (cycle.val (lower (-1))).val.coeff (exponent 1 2) -
      6 * (cycle.val (lower (-1))).val.coeff (exponent 0 3) = 0 := by
    convert first using 1
    simp [lower]
    ring
  have secondNormalized : -6 * (cycle.val (lower (-1))).val.coeff (exponent 3 0) +
      9 * (cycle.val (lower (-1))).val.coeff (exponent 2 1) -
      9 * (cycle.val (lower (-1))).val.coeff (exponent 1 2) = 0 := by
    convert second using 1
    simp [lower]
    ring
  refine ⟨trailingZero, ?_, ?_⟩
  · linear_combination - firstNormalized - 6 * trailingZero
  · linear_combination - (1 / 6 : ℂ) * secondNormalized -
      (3 / 2 : ℂ) * firstNormalized - 9 * trailingZero

def secondCube (scalar : ℂ) : Binary.HomogeneousPoly 3 :=
  ⟨C scalar * X 1 ^ 3, isHomogeneous_C_mul_X_pow scalar 1 3⟩

theorem secondCube_action (matrix : binaryArithmeticLevel) (scalar : ℂ) :
    (binaryArithmeticRepresentation 2 matrix (secondCube scalar)).val =
      C scalar * (C (matrix.val.inv 1 0 : ℂ) * X 0 +
        C (matrix.val.inv 1 1 : ℂ) * X 1) ^ 3 := by
  have different : ∀ first : Fin 4, first ≠ 0 →
      Finsupp.single (1 : Fin 2) 3 ≠ exponent first.val (3 - first.val) := by
    intro first nonzero equality
    apply nonzero
    apply Fin.ext
    have coordinate := congrArg (fun value : Fin 2 →₀ ℕ => value 0) equality
    simpa [exponent] using coordinate.symm
  have first : Finsupp.single (1 : Fin 2) 3 ≠ exponent 3 0 := different 3 (by decide)
  have second : Finsupp.single (1 : Fin 2) 3 ≠ exponent 2 1 := different 2 (by decide)
  have third : Finsupp.single (1 : Fin 2) 3 ≠ exponent 1 2 := different 1 (by decide)
  simp only [exponent, Finsupp.single_zero, add_zero] at first
  change Finsupp.single (1 : Fin 2) 3 ≠ Finsupp.single 0 2 + Finsupp.single 1 1 at second
  change Finsupp.single (1 : Fin 2) 3 ≠ Finsupp.single 0 1 + Finsupp.single 1 2 at third
  rw [cubic_action]
  simp [secondCube, exponent, X, monomial_pow, first, second, third]

theorem secondCube_upper (scalar : ℂ) :
    binaryArithmeticRepresentation 2 (upper 1) (secondCube scalar) = secondCube scalar := by
  apply Subtype.ext
  rw [secondCube_action]
  simp [upper, secondCube]

theorem secondCube_reflection (scalar : ℂ) :
    binaryArithmeticRepresentation 2 reflection (secondCube scalar) = secondCube scalar := by
  apply Subtype.ext
  rw [secondCube_action]
  simp [reflection, secondCube]

theorem secondCube_lower (scalar : ℂ) :
    (binaryArithmeticRepresentation 2 (lower (-1)) (secondCube scalar)).val -
      (secondCube scalar).val =
        C (27 * scalar) * X 0 ^ 3 + C (27 * scalar) * (X 0 ^ 2 * X 1) +
          C (9 * scalar) * (X 0 * X 1 ^ 2) := by
  rw [secondCube_action]
  norm_num [lower, secondCube]
  simp only [map_ofNat]
  ring

theorem lower_primitive
    (cycle : crossedCocycles (binaryArithmeticRepresentation 2))
    (upperZero : cycle.val (upper 1) = 0)
    (parabolic : (crossedBoundaries (binaryArithmeticRepresentation 2)).mkQ cycle ∈
      binaryParabolicH1 2) :
    cycle.val (lower (-1)) =
      binaryArithmeticRepresentation 2 (lower (-1))
        (secondCube ((cycle.val (lower (-1))).val.coeff (exponent 1 2) / 9)) -
      secondCube ((cycle.val (lower (-1))).val.coeff (exponent 1 2) / 9) := by
  obtain ⟨trailing, middle, leading⟩ := lower_cocycle_cubic_relation cycle upperZero parabolic
  apply Subtype.ext
  change (cycle.val (lower (-1))).val = _ - _
  rw [secondCube_lower]
  conv_lhs => rw [cubic_expansion]
  have leadingCorrection : (cycle.val (lower (-1))).val.coeff (exponent 3 0) =
      27 * ((cycle.val (lower (-1))).val.coeff (exponent 1 2) / 9) := by
    linear_combination leading
  have middleCorrection : (cycle.val (lower (-1))).val.coeff (exponent 2 1) =
      27 * ((cycle.val (lower (-1))).val.coeff (exponent 1 2) / 9) := by
    linear_combination middle
  have lowerCorrection : (cycle.val (lower (-1))).val.coeff (exponent 1 2) =
      9 * ((cycle.val (lower (-1))).val.coeff (exponent 1 2) / 9) := by ring
  rw [leadingCorrection, middleCorrection, trailing]
  conv_lhs => rw [lowerCorrection]
  simp

theorem normalized_parabolic_cocycle_boundary
    (cycle : crossedCocycles (binaryArithmeticRepresentation 2))
    (upperZero : cycle.val (upper 1) = 0)
    (parabolic : (crossedBoundaries (binaryArithmeticRepresentation 2)).mkQ cycle ∈
      binaryParabolicH1 2) : cycle ∈ crossedBoundaries (binaryArithmeticRepresentation 2) := by
  let correction := secondCube ((cycle.val (lower (-1))).val.coeff (exponent 1 2) / 9)
  let finalCycle := cycle - crossedBoundary (binaryArithmeticRepresentation 2) correction
  have finalUpper : finalCycle.val (upper 1) = 0 := by
    change cycle.val (upper 1) -
      (binaryArithmeticRepresentation 2 (upper 1) correction - correction) = 0
    rw [upperZero, secondCube_upper, sub_self, sub_self]
  have finalLower : finalCycle.val (lower (-1)) = 0 := by
    change cycle.val (lower (-1)) -
      (binaryArithmeticRepresentation 2 (lower (-1)) correction - correction) = 0
    rw [lower_primitive cycle upperZero parabolic]
    exact sub_self _
  have finalReflection : finalCycle.val reflection = 0 := by
    change cycle.val reflection -
      (binaryArithmeticRepresentation 2 reflection correction - correction) = 0
    rw [reflection_cocycle_zero cycle upperZero, secondCube_reflection, sub_self, sub_self]
  have finalZero := cocycle_zero_of_generators finalCycle finalUpper finalLower finalReflection
  exact ⟨correction, (sub_eq_zero.mp finalZero).symm⟩

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

theorem parabolic_cocycle_boundary
    (cycle : crossedCocycles (binaryArithmeticRepresentation 2))
    (parabolic : (crossedBoundaries (binaryArithmeticRepresentation 2)).mkQ cycle ∈
      binaryParabolicH1 2) : cycle ∈ crossedBoundaries (binaryArithmeticRepresentation 2) :=
  boundary_of_normalized (binaryArithmeticRepresentation 2) (binaryParabolicH1 2) (upper 1)
    (fun cycle membership => parabolic_generator_primitive cycle membership 1 (upper 1) upper_cusp)
    normalized_parabolic_cocycle_boundary cycle parabolic

private theorem crossed_submodule_eq_bot {GroupType Value : Type} [Group GroupType]
    [AddCommGroup Value] [Module ℂ Value] (representation : Representation ℂ GroupType Value)
    (inner : Submodule ℂ (CrossedH1 representation))
    (vanishing : ∀ cycle : crossedCocycles representation,
      (crossedBoundaries representation).mkQ cycle ∈ inner → cycle ∈ crossedBoundaries representation) :
    inner = ⊥ := by
  apply le_antisymm
  · intro coordinate membership
    obtain ⟨cycle, rfl⟩ := (crossedBoundaries representation).mkQ_surjective coordinate
    exact (Submodule.Quotient.mk_eq_zero _).mpr (vanishing cycle membership)
  · exact bot_le

theorem binaryParabolicH1_degree_two_eq_bot : binaryParabolicH1 2 = ⊥ :=
  crossed_submodule_eq_bot (binaryArithmeticRepresentation 2) (binaryParabolicH1 2)
    parabolic_cocycle_boundary

theorem innerBadLineClasses_degree_two_eq_bot : innerBadLineClasses 2 = ⊥ := by
  apply le_antisymm
  · intro coordinate membership
    let innerClass : innerBadLineClasses 2 := ⟨coordinate, membership⟩
    have mappedZero : innerBadLineParabolicMap 2 (by omega) innerClass = 0 := by
      apply Subtype.ext
      exact (Submodule.mem_bot ℂ).mp (binaryParabolicH1_degree_two_eq_bot ▸
        (innerBadLineParabolicMap 2 (by omega) innerClass).property)
    have zero := (innerBadLineParabolicMap_zero_iff 2 (by omega) innerClass).mp mappedZero
    exact congrArg Subtype.val zero
  · exact bot_le

theorem inner_bad_line_degree_two_zero (coordinate : StratumH2 2 trivialCharacter .line)
    (good : VanishesOnGood 2 trivialCharacter .line coordinate)
    (inner : InnerBoundary 2 trivialCharacter .line coordinate) : coordinate = 0 := by
  have membership := (mem_innerBadLineClasses_iff 2 coordinate).mpr ⟨good, inner⟩
  rw [innerBadLineClasses_degree_two_eq_bot] at membership
  exact membership

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.DegreeTwoVanishing
