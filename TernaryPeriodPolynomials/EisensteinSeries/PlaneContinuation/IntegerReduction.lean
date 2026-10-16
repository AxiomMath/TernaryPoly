module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FlagRows
public import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction

theorem exists_binary_gcd_matrix (first second : ℤ) :
    ∃ matrix : Matrix.GeneralLinearGroup (Fin 2) ℤ,
      first * matrix.val 0 0 + second * matrix.val 1 0 = 0 ∧
      first * matrix.val 0 1 + second * matrix.val 1 1 = (Int.gcd first second : ℤ) := by
  by_cases zeroGcd : Int.gcd first second = 0
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp zeroGcd
    exact ⟨1, by simp⟩
  · have nonzeroGcd : (Int.gcd first second : ℤ) ≠ 0 := by exact_mod_cast zeroGcd
    have firstDivision := Int.ediv_mul_cancel (Int.gcd_dvd_left first second)
    have secondDivision := Int.ediv_mul_cancel (Int.gcd_dvd_right first second)
    have bezout := Int.gcd_eq_gcd_ab first second
    have reducedBezout : first / (Int.gcd first second : ℤ) * Int.gcdA first second +
        second / (Int.gcd first second : ℤ) * Int.gcdB first second = 1 := by
      apply (mul_right_inj' nonzeroGcd).mp
      linear_combination Int.gcdA first second * firstDivision +
        Int.gcdB first second * secondDivision - bezout
    let matrix : Matrix.GeneralLinearGroup (Fin 2) ℤ :=
      ⟨!![second / (Int.gcd first second : ℤ), Int.gcdA first second;
          -(first / (Int.gcd first second : ℤ)), Int.gcdB first second],
        !![Int.gcdB first second, -Int.gcdA first second;
          first / (Int.gcd first second : ℤ), second / (Int.gcd first second : ℤ)], by
          apply Matrix.ext
          intro row column
          fin_cases row <;> fin_cases column <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [reducedBezout], by
          apply Matrix.ext
          intro row column
          fin_cases row <;> fin_cases column <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [reducedBezout]⟩
    refine ⟨matrix, ?_, ?_⟩
    · change first * (second / (Int.gcd first second : ℤ)) +
        second * -(first / (Int.gcd first second : ℤ)) = 0
      apply (mul_right_inj' nonzeroGcd).mp
      linear_combination first * secondDivision - second * firstDivision
    · exact bezout.symm

theorem exists_integer_lastRow_reduction (rowVector : Fin 3 → ℤ) :
    ∃ matrix : IntegralGL3,
      (rowVector ᵥ* matrix.val) 0 = 0 ∧
      (rowVector ᵥ* matrix.val) 1 = 0 ∧
      (rowVector ᵥ* matrix.val) 2 =
        (Int.gcd (Int.gcd (rowVector 0) (rowVector 1) : ℤ) (rowVector 2) : ℤ) := by
  obtain ⟨firstMatrix, firstZero, firstGcd⟩ :=
    exists_binary_gcd_matrix (rowVector 0) (rowVector 1)
  obtain ⟨secondMatrix, secondZero, secondGcd⟩ :=
    exists_binary_gcd_matrix (Int.gcd (rowVector 0) (rowVector 1) : ℤ) (rowVector 2)
  have firstRow : rowVector ᵥ* (planeLevi firstMatrix 1).val =
      ![0, (Int.gcd (rowVector 0) (rowVector 1) : ℤ), rowVector 2] := by
    funext column
    fin_cases column <;>
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, planeLevi, planeBlock,
        firstZero, firstGcd]
  refine ⟨planeLevi firstMatrix 1 * lineLevi 1 secondMatrix, ?_⟩
  simp only [Units.val_mul, ← Matrix.vecMul_vecMul, firstRow]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, lineLevi, planeLevi, planeBlock,
    weyl, Matrix.mul_apply, secondZero, secondGcd]

theorem exists_rational_lastRow_reduction (rowVector : Fin 3 → ℚ) :
    ∃ matrix : IntegralGL3,
      (rowVector ᵥ* (integralRational matrix).val) 0 = 0 ∧
      (rowVector ᵥ* (integralRational matrix).val) 1 = 0 := by
  obtain ⟨denominator, integerValues⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) rowVector
  choose integerRow rowEquality using integerValues
  have nonzeroDenominator : (denominator.val : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (nonZeroDivisors.coe_ne_zero denominator)
  have rowEquality' (column : Fin 3) :
      (integerRow column : ℚ) = (denominator.val : ℚ) * rowVector column := by
    simpa [Algebra.smul_def, algebraMap_int_eq, Int.castRingHom] using rowEquality column
  obtain ⟨matrix, firstZero, secondZero, _⟩ := exists_integer_lastRow_reduction integerRow
  have scaledProduct (column : Fin 3) :
      (denominator.val : ℚ) * (rowVector ᵥ* (integralRational matrix).val) column =
        ((integerRow ᵥ* matrix.val) column : ℚ) := by
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl
    intro index _
    rw [rowEquality', mul_assoc]
    rfl
  refine ⟨matrix, ?_, ?_⟩
  · apply (mul_eq_zero.mp ((scaledProduct 0).trans (by rw [firstZero, Int.cast_zero]))).resolve_left
      nonzeroDenominator
  · apply (mul_eq_zero.mp ((scaledProduct 1).trans (by rw [secondZero, Int.cast_zero]))).resolve_left
      nonzeroDenominator

theorem exists_rational_plane_integral (matrix : RationalGL3) :
    ∃ (parabolicElement : planeParabolic ℚ) (integralMatrix : IntegralGL3),
      matrix = parabolicElement.val * integralRational integralMatrix := by
  obtain ⟨integralMatrix, firstZero, secondZero⟩ :=
    exists_rational_lastRow_reduction (matrix.val 2)
  have parabolicMembership : InPlaneParabolic (matrix * integralRational integralMatrix) :=
    ⟨firstZero, secondZero⟩
  refine ⟨⟨matrix * integralRational integralMatrix, parabolicMembership⟩,
    integralMatrix⁻¹, ?_⟩
  change matrix = (matrix * integralRational integralMatrix) * integralRational integralMatrix⁻¹
  rw [map_inv, mul_inv_cancel_right]

theorem exists_integral_flag (flag : Flags .plane) :
    ∃ integralMatrix : IntegralGL3, QuotientGroup.mk (integralRational integralMatrix) = flag := by
  obtain ⟨integralMatrix, firstZero, secondZero⟩ :=
    exists_rational_lastRow_reduction ((flag.out⁻¹).val 2)
  refine ⟨integralMatrix, ?_⟩
  have flagEquality : (QuotientGroup.mk flag.out : Flags .plane) =
      QuotientGroup.mk (integralRational integralMatrix) := by
    apply QuotientGroup.eq.mpr
    exact ⟨firstZero, secondZero⟩
  simpa only [QuotientGroup.mk, Quotient.out_eq] using flagEquality.symm

noncomputable def integralFlagRepresentative (flag : Flags .plane) : IntegralGL3 :=
  Classical.choose (exists_integral_flag flag)

theorem integralFlagRepresentative_mk (flag : Flags .plane) :
    QuotientGroup.mk (integralRational (integralFlagRepresentative flag)) = flag :=
  Classical.choose_spec (exists_integral_flag flag)

noncomputable def integralFlagRow (flag : Flags .plane) (column : Fin 3) : ℤ :=
  ((integralFlagRepresentative flag)⁻¹).val 2 column

theorem integralFlagRow_ne_zero (flag : Flags .plane) : integralFlagRow flag ≠ 0 :=
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlagRows.lastRow_ne_zero (integralFlagRepresentative flag)⁻¹

theorem integralFlagRow_primitive (flag : Flags .plane) :
    ∃ coefficients : Fin 3 → ℤ,
      ∑ column : Fin 3, integralFlagRow flag column * coefficients column = 1 := by
  refine ⟨fun column => (integralFlagRepresentative flag).val column 2, ?_⟩
  have identityEntry := congrArg
    (fun value : Matrix (Fin 3) (Fin 3) ℤ => value 2 2)
    (integralFlagRepresentative flag).inv_mul
  simpa only [integralFlagRow, GeneralLinearGroup.coe_inv, Matrix.mul_apply,
    Matrix.one_apply_eq] using identityEntry

theorem integralFlagRow_injective : Function.Injective integralFlagRow := by
  intro first second rowsEquality
  rw [← integralFlagRepresentative_mk first, ← integralFlagRepresentative_mk second]
  apply (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlagRows.planeFlag_eq_iff_rows _ _).mpr
  refine ⟨1, fun column => ?_⟩
  simp only [Units.val_one, one_mul]
  change (integralFlagRow first column : ℚ) = (integralFlagRow second column : ℚ)
  exact congrArg Int.cast (congrFun rowsEquality column)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction
