module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.IntegralConjugation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section


open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.BoundaryFiniteness.IntegerRowReduction

noncomputable section

theorem bezout_divided (a b : ℤ) (nonzero : Int.gcd a b ≠ 0) :
    Int.gcdA a b * (a / (Int.gcd a b : ℤ)) + Int.gcdB a b * (b / (Int.gcd a b : ℤ)) = 1 := by
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr nonzero : (Int.gcd a b : ℤ) ≠ 0)
  calc
    (Int.gcd a b : ℤ) * (Int.gcdA a b * (a / (Int.gcd a b : ℤ)) +
        Int.gcdB a b * (b / (Int.gcd a b : ℤ))) =
      Int.gcdA a b * ((Int.gcd a b : ℤ) * (a / (Int.gcd a b : ℤ))) +
        Int.gcdB a b * ((Int.gcd a b : ℤ) * (b / (Int.gcd a b : ℤ))) := by ring
    _ = Int.gcdA a b * a + Int.gcdB a b * b := by
      rw [Int.mul_ediv_cancel' (Int.gcd_dvd_left a b), Int.mul_ediv_cancel' (Int.gcd_dvd_right a b)]
    _ = (Int.gcd a b : ℤ) * 1 := by rw [Int.gcd_eq_gcd_ab]; ring

def pairMatrix (a b : ℤ) : GeneralLinearGroup (Fin 2) ℤ := by
  classical
  exact if zero : Int.gcd a b = 0 then 1 else
    GeneralLinearGroup.mk'' !![Int.gcdA a b, -(b / (Int.gcd a b : ℤ));
      Int.gcdB a b, a / (Int.gcd a b : ℤ)] (by
        have determinant := bezout_divided a b zero
        rw [Matrix.det_fin_two]
        simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, neg_mul, sub_neg_eq_add]
        rw [mul_comm (b / (Int.gcd a b : ℤ)), determinant]
        exact isUnit_one)

theorem pair_first (a b : ℤ) :
    a * (pairMatrix a b).val 0 0 + b * (pairMatrix a b).val 1 0 = Int.gcd a b := by
  classical
  unfold pairMatrix
  split_ifs with zero
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp zero
    simp
  · exact (Int.gcd_eq_gcd_ab a b).symm

theorem pair_last (a b : ℤ) :
    a * (pairMatrix a b).val 0 1 + b * (pairMatrix a b).val 1 1 = 0 := by
  classical
  unfold pairMatrix
  split_ifs with zero
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp zero
    simp
  · change a * -(b / (Int.gcd a b : ℤ)) + b * (a / (Int.gcd a b : ℤ)) = 0
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr zero : (Int.gcd a b : ℤ) ≠ 0)
    calc
      (Int.gcd a b : ℤ) * (a * -(b / (Int.gcd a b : ℤ)) + b * (a / (Int.gcd a b : ℤ))) =
          -(a * ((Int.gcd a b : ℤ) * (b / (Int.gcd a b : ℤ)))) +
            b * ((Int.gcd a b : ℤ) * (a / (Int.gcd a b : ℤ))) := by ring
      _ = (Int.gcd a b : ℤ) * 0 := by
        rw [Int.mul_ediv_cancel' (Int.gcd_dvd_left a b), Int.mul_ediv_cancel' (Int.gcd_dvd_right a b)]
        ring

def firstBlock (matrix : GeneralLinearGroup (Fin 2) ℤ) : IntegralGL3 :=
  Adelic.planeLevi matrix 1

def secondBlock (matrix : GeneralLinearGroup (Fin 2) ℤ) : IntegralGL3 :=
  GeneralLinearGroup.mk'' !![matrix.val 0 0, 0, matrix.val 0 1;
    0, 1, 0; matrix.val 1 0, 0, matrix.val 1 1] (by
      have unit := (Matrix.isUnit_iff_isUnit_det matrix.val).mp matrix.isUnit
      simpa [Matrix.det_fin_three, Matrix.det_fin_two] using unit)

theorem firstBlock_row (row : Fin 3 → ℤ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    row ᵥ* (firstBlock matrix).val =
      ![row 0 * matrix.val 0 0 + row 1 * matrix.val 1 0,
        row 0 * matrix.val 0 1 + row 1 * matrix.val 1 1, row 2] := by
  funext index
  fin_cases index <;>
    simp [firstBlock, Adelic.planeLevi, Adelic.planeBlock, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem secondBlock_row (row : Fin 3 → ℤ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    row ᵥ* (secondBlock matrix).val =
      ![row 0 * matrix.val 0 0 + row 2 * matrix.val 1 0, row 1,
        row 0 * matrix.val 0 1 + row 2 * matrix.val 1 1] := by
  funext index
  fin_cases index <;>
    simp [secondBlock, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

def reduceRow (row : Fin 3 → ℤ) : IntegralGL3 :=
  firstBlock (pairMatrix (row 0) (row 1)) *
    secondBlock (pairMatrix (Int.gcd (row 0) (row 1)) (row 2))

theorem reduceRow_spec (row : Fin 3 → ℤ) :
    row ᵥ* (reduceRow row).val = ![(Int.gcd (Int.gcd (row 0) (row 1)) (row 2) : ℤ), 0, 0] := by
  unfold reduceRow
  rw [GeneralLinearGroup.coe_mul, ← Matrix.vecMul_vecMul, firstBlock_row]
  rw [pair_first, pair_last, secondBlock_row]
  simp [pair_first, pair_last]

theorem reduceRow_nonzero (row : Fin 3 → ℤ) (nonzero : row ≠ 0) :
    (Int.gcd (Int.gcd (row 0) (row 1)) (row 2) : ℤ) ≠ 0 := by
  intro zero
  have outer := Int.gcd_eq_zero_iff.mp (Nat.cast_eq_zero.mp zero)
  have inner := Int.gcd_eq_zero_iff.mp (Nat.cast_eq_zero.mp outer.1)
  apply nonzero
  funext index
  fin_cases index <;> simp [inner.1, inner.2, outer.2]

end

end TernaryPeriodPolynomials.BoundaryFiniteness.IntegerRowReduction
