module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalSmith
public import Mathlib.Data.Int.GCD

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.IntegerRows

theorem binary_reduction (first second : ℤ) :
    ∃ matrix : GeneralLinearGroup (Fin 2) ℤ,
      ![first, second] ᵥ* matrix.val = ![(first.gcd second : ℤ), 0] := by
  by_cases zero : first.gcd second = 0
  · have both : first = 0 ∧ second = 0 := Int.gcd_eq_zero_iff.mp zero
    exact ⟨1, by simp [both.1, both.2]⟩
  have nonzero : (first.gcd second : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr zero
  let divisor : ℤ := first.gcd second
  let a := first.gcdA second
  let b := first.gcdB second
  let x := first / divisor
  let y := second / divisor
  have firstEquality : x * divisor = first := Int.ediv_mul_cancel (Int.gcd_dvd_left first second)
  have secondEquality : y * divisor = second := Int.ediv_mul_cancel (Int.gcd_dvd_right first second)
  have bezout : first * a + second * b = divisor := (Int.gcd_eq_gcd_ab first second).symm
  have determinant : a * x + b * y = 1 := by
    apply mul_right_cancel₀ nonzero
    change (a * x + b * y) * divisor = 1 * divisor
    rw [add_mul, mul_assoc, firstEquality, mul_assoc, secondEquality, one_mul]
    simpa only [mul_comm] using bezout
  let matrix : GeneralLinearGroup (Fin 2) ℤ :=
    { val := !![a, -y; b, x]
      inv := !![x, y; -b, a]
      val_inv := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith [determinant]
      inv_val := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith [determinant] }
  refine ⟨matrix, ?_⟩
  ext i
  fin_cases i
  · simpa [matrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using bezout
  · simp [matrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    nlinarith [congrArg (fun z => z * y) firstEquality,
      congrArg (fun z => z * x) secondEquality]

theorem ternary_reduction (row : Fin 3 → ℤ) :
    ∃ matrix : IntegralGL3, ∃ divisor : ℤ,
      row ᵥ* matrix.val = ![0, 0, divisor] := by
  obtain ⟨first, firstEquality⟩ := binary_reduction (row 0) (row 1)
  let firstBlock : IntegralGL3 := planeLevi first 1
  let rotated : IntegralGL3 := firstBlock * weyl
  have rotatedRow : row ᵥ* rotated.val = ![0, row 2, ((row 0).gcd (row 1) : ℤ)] := by
    have eq0 := congrFun firstEquality 0
    have eq1 := congrFun firstEquality 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at eq0 eq1
    ext i
    fin_cases i <;>
      simp [rotated, firstBlock, planeLevi, planeBlock, weyl, Matrix.vecMul, dotProduct,
        Matrix.mul_apply, Fin.sum_univ_succ] <;> first | exact eq0 | exact eq1
  obtain ⟨last, lastEquality⟩ := binary_reduction (row 2) ((row 0).gcd (row 1))
  let swap : GeneralLinearGroup (Fin 2) ℤ :=
    { val := !![0, 1; 1, 0]
      inv := !![0, 1; 1, 0]
      val_inv := by decide
      inv_val := by decide }
  let matrix := rotated * lineLevi 1 (last * swap)
  refine ⟨matrix, (row 2).gcd ((row 0).gcd (row 1)), ?_⟩
  have equality : row ᵥ* matrix.val = (row ᵥ* rotated.val) ᵥ* (lineLevi 1 (last * swap)).val :=
    (Matrix.vecMul_vecMul _ _ _).symm
  rw [equality, rotatedRow]
  have eq0 := congrFun lastEquality 0
  have eq1 := congrFun lastEquality 1
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at eq0 eq1
  ext i
  fin_cases i <;>
    simp [lineLevi_val, swap, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | exact eq0 | exact eq1

theorem rational_reduction (row : Fin 3 → ℚ) :
    ∃ matrix : IntegralGL3,
      (row ᵥ* (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix).val) 0 = 0 ∧
      (row ᵥ* (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix).val) 1 = 0 := by
  obtain ⟨denominator, nonzero, integerMatrix, equality⟩ :=
    RationalSmith.clear_denominators (fun _ : Fin 3 => row)
  have entries : ∀ index, (integerMatrix 0 index : ℚ) = (denominator : ℚ) * row index :=
    fun index => congrArg (fun matrix => matrix 0 index) equality
  obtain ⟨matrix, divisor, reduction⟩ := ternary_reduction (integerMatrix 0)
  have scalarNonzero : (denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr nonzero
  have zeroColumn : ∀ column : Fin 3, column ≠ 2 →
      (row ᵥ* (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix).val) column = 0 := by
    intro column different
    have integralZero : ((integerMatrix 0) ᵥ* matrix.val) column = 0 := by
      rw [reduction]
      fin_cases column <;> simp_all
    have rationalZero := congrArg (Int.cast : ℤ → ℚ) integralZero
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at rationalZero
    rw [entries 0, entries 1, entries 2] at rationalZero
    apply (mul_eq_zero.mp (show (denominator : ℚ) *
      (row ᵥ* (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix).val) column = 0 from ?_)).resolve_left
      scalarNonzero
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, mul_add, mul_assoc] using rationalZero
  exact ⟨matrix, zeroColumn 0 (by decide), zeroColumn 1 (by decide)⟩

theorem integral_flag_representative (flag : Flags .plane) :
    ∃ matrix : IntegralGL3,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) : Flags .plane) = flag := by
  induction flag using Quotient.inductionOn with
  | h representative =>
    obtain ⟨matrix, zeroFirst, zeroSecond⟩ := rational_reduction ((representative⁻¹).val 2)
    refine ⟨matrix, ?_⟩
    symm
    apply QuotientGroup.eq.mpr
    exact ⟨zeroFirst, zeroSecond⟩

def flagRepresentative (flag : Flags .plane) : IntegralGL3 :=
  Classical.choose (integral_flag_representative flag)

theorem flagRepresentative_spec (flag : Flags .plane) :
    (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) (flagRepresentative flag)) :
      Flags .plane) = flag :=
  Classical.choose_spec (integral_flag_representative flag)

def flagRow (flag : Flags .plane) : Fin 3 → ℤ := (flagRepresentative flag).inv 2

theorem flagRow_primitive (flag : Flags .plane) :
    ∃ coefficients : Fin 3 → ℤ, ∑ index, flagRow flag index * coefficients index = 1 := by
  refine ⟨fun index => (flagRepresentative flag).val index 2, ?_⟩
  exact congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℤ => matrix 2 2)
    (flagRepresentative flag).inv_val

theorem flagRow_nonzero (flag : Flags .plane) : flagRow flag ≠ 0 := by
  intro zero
  obtain ⟨coefficients, primitive⟩ := flagRow_primitive flag
  rw [zero] at primitive
  simp at primitive

theorem flagRow_injective : Function.Injective flagRow := by
  intro first second equality
  rw [← flagRepresentative_spec first, ← flagRepresentative_spec second]
  apply QuotientGroup.eq.mpr
  have rowEquality : (flagRepresentative first).inv 2 = (flagRepresentative second).inv 2 := equality
  have product : ∀ column : Fin 3,
      ((flagRepresentative first).inv * (flagRepresentative second).val) 2 column =
        (1 : Matrix (Fin 3) (Fin 3) ℤ) 2 column := by
    intro column
    change ((flagRepresentative first).inv 2 ᵥ* (flagRepresentative second).val) column = _
    rw [rowEquality]
    exact congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℤ => matrix 2 column)
      (flagRepresentative second).inv_val
  change (GeneralLinearGroup.map (Int.castRingHom ℚ) (flagRepresentative first))⁻¹ *
    GeneralLinearGroup.map (Int.castRingHom ℚ) (flagRepresentative second) ∈ planeParabolic ℚ
  rw [← map_inv, ← map_mul]
  constructor
  · change (Int.castRingHom ℚ) (((flagRepresentative first).inv *
      (flagRepresentative second).val) 2 0) = 0
    rw [product]
    norm_num [Matrix.one_apply]
  · change (Int.castRingHom ℚ) (((flagRepresentative first).inv *
      (flagRepresentative second).val) 2 1) = 0
    rw [product]
    norm_num [Matrix.one_apply]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.IntegerRows
