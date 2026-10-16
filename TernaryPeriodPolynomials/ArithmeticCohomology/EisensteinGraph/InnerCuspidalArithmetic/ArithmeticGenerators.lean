module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerParabolic

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators

open Helpers

theorem balanced_remainder_positive (value modulus : ℤ) (positive : 0 < modulus) :
    ∃ multiple : ℤ, 2 * |value + multiple * modulus| ≤ modulus := by
  have nonnegative := Int.emod_nonneg value (ne_of_gt positive)
  have bounded := Int.emod_lt_of_pos value positive
  have division := Int.ediv_mul_add_emod value modulus
  by_cases lower : 2 * (value % modulus) ≤ modulus
  · refine ⟨-(value / modulus), ?_⟩
    have remainder : value + -(value / modulus) * modulus = value % modulus := by
      nlinarith [division]
    rw [remainder, abs_of_nonneg nonnegative]
    exact lower
  · refine ⟨-(value / modulus) - 1, ?_⟩
    have remainder : value + (-(value / modulus) - 1) * modulus = value % modulus - modulus := by
      nlinarith [division]
    rw [remainder, abs_of_nonpos (by omega)]
    omega

theorem balanced_remainder (value modulus : ℤ) (nonzero : modulus ≠ 0) :
    ∃ multiple : ℤ, 2 * |value + multiple * modulus| ≤ |modulus| := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · obtain ⟨multiple, bound⟩ := balanced_remainder_positive value (-modulus) (by omega)
    refine ⟨-multiple, ?_⟩
    rw [abs_of_neg negative]
    simpa only [mul_neg, neg_mul, neg_neg] using bound
  · simpa only [abs_of_pos positive] using balanced_remainder_positive value modulus positive

def upper (parameter : ℤ) : binaryArithmeticLevel :=
  ⟨⟨!![1, parameter; 0, 1], !![1, -parameter; 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, by
    apply (mem_binaryArithmeticLevel_iff _).mpr
    intro column
    fin_cases column <;> rfl⟩

def lower (parameter : ℤ) : binaryArithmeticLevel :=
  ⟨⟨!![1, 0; 3 * parameter, 1], !![1, 0; -(3 * parameter), 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, by
    apply (mem_binaryArithmeticLevel_iff _).mpr
    intro column
    have cast_three : (3 : ZMod 3) = 0 := by decide
    fin_cases column <;> simp [cast_three]⟩

def reflection : binaryArithmeticLevel :=
  ⟨⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by decide, by decide⟩, by
    apply (mem_binaryArithmeticLevel_iff _).mpr
    intro column
    fin_cases column <;> rfl⟩

theorem upper_mul (first second : ℤ) : upper first * upper second = upper (first + second) := by
  apply Subtype.ext
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lower_mul (first second : ℤ) : lower first * lower second = lower (first + second) := by
  apply Subtype.ext
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [lower, Matrix.mul_apply, Fin.sum_univ_two, mul_add]

def upperHom : Multiplicative ℤ →* binaryArithmeticLevel where
  toFun parameter := upper parameter.toAdd
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;> rfl
  map_mul' first second := (upper_mul first.toAdd second.toAdd).symm

def lowerHom : Multiplicative ℤ →* binaryArithmeticLevel where
  toFun parameter := lower parameter.toAdd
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;> rfl
  map_mul' first second := (lower_mul first.toAdd second.toAdd).symm

theorem upper_zpow (parameter : ℤ) : upper parameter = upper 1 ^ parameter := by
  change upperHom (Multiplicative.ofAdd parameter) = upperHom (Multiplicative.ofAdd 1) ^ parameter
  rw [← map_zpow]
  congr 1
  exact Multiplicative.toAdd.injective (by simp)

theorem lower_zpow (parameter : ℤ) : lower parameter = lower 1 ^ parameter := by
  change lowerHom (Multiplicative.ofAdd parameter) = lowerHom (Multiplicative.ofAdd 1) ^ parameter
  rw [← map_zpow]
  congr 1
  exact Multiplicative.toAdd.injective (by simp)

def generated : Subgroup binaryArithmeticLevel := Subgroup.closure {upper 1, lower 1, reflection}

theorem upper_mem (parameter : ℤ) : upper parameter ∈ generated := by
  rw [upper_zpow]
  exact generated.zpow_mem (Subgroup.subset_closure (by simp)) parameter

theorem lower_mem (parameter : ℤ) : lower parameter ∈ generated := by
  rw [lower_zpow]
  exact generated.zpow_mem (Subgroup.subset_closure (by simp)) parameter

theorem reflection_mem : reflection ∈ generated := Subgroup.subset_closure (by simp)

theorem mem_generated_of_lower_zero (matrix : binaryArithmeticLevel)
    (lowerZero : matrix.val.val 1 0 = 0) : matrix ∈ generated := by
  have determinant := Int.units_eq_one_or (GeneralLinearGroup.det matrix.val)
  have diagonal : matrix.val.val 0 0 * matrix.val.val 1 1 = 1 ∨
      matrix.val.val 0 0 * matrix.val.val 1 1 = -1 := by
    rcases determinant with positive | negative
    · left
      have equation := congrArg Units.val positive
      simpa only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, lowerZero,
        mul_zero, sub_zero, Units.val_one] using equation
    · right
      have equation := congrArg Units.val negative
      simpa only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, lowerZero,
        mul_zero, sub_zero, Units.val_neg, Units.val_one] using equation
  have bottom : matrix.val.val 1 1 = 1 ∨ matrix.val.val 1 1 = -1 := by
    rcases diagonal with positive | negative
    · exact Int.eq_one_or_neg_one_of_mul_eq_one (by simpa only [mul_comm] using positive)
    · have equation : (-matrix.val.val 0 0) * matrix.val.val 1 1 = 1 := by nlinarith
      exact Int.eq_one_or_neg_one_of_mul_eq_one (by simpa only [mul_comm] using equation)
  have congruence := (mem_binaryArithmeticLevel_iff matrix.val).mp matrix.property 1
  have bottomOne : matrix.val.val 1 1 = 1 := by
    rcases bottom with positive | negative
    · exact positive
    · rw [negative] at congruence
      exact False.elim ((by decide : (-1 : ZMod 3) ≠ 1) congruence)
  have top : matrix.val.val 0 0 = 1 ∨ matrix.val.val 0 0 = -1 := by
    simpa only [bottomOne, mul_one] using diagonal
  rcases top with positive | negative
  · have equality : matrix = upper (matrix.val.val 0 1) := by
      apply Subtype.ext
      apply Units.ext
      ext row column
      fin_cases row <;> fin_cases column <;> simp [upper, positive, lowerZero, bottomOne]
    rw [equality]
    exact upper_mem _
  · have equality : matrix = upper (matrix.val.val 0 1) * reflection := by
      apply Subtype.ext
      apply Units.ext
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [upper, reflection, Matrix.mul_apply, Fin.sum_univ_two, negative, lowerZero, bottomOne]
    rw [equality]
    exact generated.mul_mem (upper_mem _) reflection_mem

theorem lower_divisible (matrix : binaryArithmeticLevel) : 3 ∣ matrix.val.val 1 0 := by
  have congruence := (mem_binaryArithmeticLevel_iff matrix.val).mp matrix.property 0
  have zero : (matrix.val.val 1 0 : ZMod 3) = 0 := by simpa using congruence
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp zero

theorem mem_generated (matrix : binaryArithmeticLevel) : matrix ∈ generated := by
  suffices inductionStep : ∀ size : ℕ, ∀ matrix : binaryArithmeticLevel,
      (matrix.val.val 1 0).natAbs = size → matrix ∈ generated from
    inductionStep _ matrix rfl
  intro size
  induction size using Nat.strong_induction_on with
  | h size inductionHypothesis =>
    intro matrix sizeEquality
    by_cases lowerZero : matrix.val.val 1 0 = 0
    · exact mem_generated_of_lower_zero matrix lowerZero
    obtain ⟨firstMultiple, firstBound⟩ := balanced_remainder (matrix.val.val 0 0)
      (matrix.val.val 1 0) lowerZero
    let firstMatrix := upper firstMultiple * matrix
    have firstTop : firstMatrix.val.val 0 0 =
        matrix.val.val 0 0 + firstMultiple * matrix.val.val 1 0 := by
      simp [firstMatrix, upper, Matrix.mul_apply, Fin.sum_univ_two]
    have firstBottom : firstMatrix.val.val 1 0 = matrix.val.val 1 0 := by
      simp [firstMatrix, upper, Matrix.mul_apply, Fin.sum_univ_two]
    have firstTopNonzero : firstMatrix.val.val 0 0 ≠ 0 := by
      intro zero
      have determinant := Int.units_eq_one_or (GeneralLinearGroup.det firstMatrix.val)
      have absoluteProduct : |firstMatrix.val.val 0 1| * |matrix.val.val 1 0| = 1 := by
        rcases determinant with positive | negative
        · have equation := congrArg Units.val positive
          simp only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, zero,
            firstBottom, zero_mul, zero_sub, Units.val_one] at equation
          have absolute := congrArg abs equation
          simpa only [Units.val_neg, Units.val_one, abs_neg, abs_mul, abs_one] using absolute
        · have equation := congrArg Units.val negative
          simp only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, zero,
            firstBottom, zero_mul, zero_sub, Units.val_neg, Units.val_one] at equation
          have absolute := congrArg abs equation
          simpa only [abs_neg, abs_mul, abs_one] using absolute
      have bottomAbs : |matrix.val.val 1 0| = 1 := by
        exact Int.eq_one_of_mul_eq_one_left (abs_nonneg _) absoluteProduct
      have bottomSquare := sq_abs (matrix.val.val 1 0)
      rw [bottomAbs] at bottomSquare
      have bottomCases : matrix.val.val 1 0 = 1 ∨ matrix.val.val 1 0 = -1 :=
        sq_eq_one_iff.mp (by nlinarith [bottomSquare])
      have divisible := lower_divisible matrix
      rcases bottomCases with positive | negative
      · rw [positive] at divisible
        norm_num at divisible
      · rw [negative] at divisible
        norm_num at divisible
    have modulusNonzero : 3 * firstMatrix.val.val 0 0 ≠ 0 :=
      mul_ne_zero (by norm_num) firstTopNonzero
    obtain ⟨secondMultiple, secondBound⟩ := balanced_remainder (firstMatrix.val.val 1 0)
      (3 * firstMatrix.val.val 0 0) modulusNonzero
    let secondMatrix := lower secondMultiple * firstMatrix
    have secondBottom : secondMatrix.val.val 1 0 = firstMatrix.val.val 1 0 +
        secondMultiple * (3 * firstMatrix.val.val 0 0) := by
      simp [secondMatrix, lower, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have firstEstimate : 2 * |firstMatrix.val.val 0 0| ≤ |matrix.val.val 1 0| := by
      rw [firstTop]
      exact firstBound
    have secondEstimate : 2 * |secondMatrix.val.val 1 0| ≤
        3 * |firstMatrix.val.val 0 0| := by
      rw [secondBottom]
      simpa only [abs_mul, show |(3 : ℤ)| = 3 by norm_num] using secondBound
    have strictDecrease : (secondMatrix.val.val 1 0).natAbs < size := by
      rw [← sizeEquality]
      have absoluteDecrease : |secondMatrix.val.val 1 0| < |matrix.val.val 1 0| := by
        have positive := abs_pos.mpr lowerZero
        omega
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs] at absoluteDecrease
      exact_mod_cast absoluteDecrease
    have smaller := inductionHypothesis _ strictDecrease secondMatrix rfl
    have restored : matrix = (upper firstMultiple)⁻¹ * (lower secondMultiple)⁻¹ * secondMatrix := by
      simp only [secondMatrix, firstMatrix, mul_assoc, inv_mul_cancel_left]
    rw [restored]
    exact generated.mul_mem (generated.mul_mem (generated.inv_mem (upper_mem _))
      (generated.inv_mem (lower_mem _))) smaller

theorem generators_span : generated = ⊤ := by
  apply top_unique
  intro matrix _
  exact mem_generated matrix

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
