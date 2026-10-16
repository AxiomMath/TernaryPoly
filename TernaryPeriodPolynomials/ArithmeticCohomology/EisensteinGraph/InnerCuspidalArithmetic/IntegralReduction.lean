module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.BadLine

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem normalizedBezout (first second : ℤ) (nonzero : first.gcd second ≠ 0) :
    (first / (first.gcd second : ℤ)) * first.gcdA second +
      (second / (first.gcd second : ℤ)) * first.gcdB second = 1 := by
  apply mul_right_cancel₀ (show (first.gcd second : ℤ) ≠ 0 by exact_mod_cast nonzero)
  calc
    ((first / (first.gcd second : ℤ)) * first.gcdA second +
        (second / (first.gcd second : ℤ)) * first.gcdB second) *
        (first.gcd second : ℤ) =
      (first / (first.gcd second : ℤ) * (first.gcd second : ℤ)) * first.gcdA second +
        (second / (first.gcd second : ℤ) * (first.gcd second : ℤ)) * first.gcdB second := by
      ring
    _ = first * first.gcdA second + second * first.gcdB second := by
      rw [Int.ediv_mul_cancel (Int.gcd_dvd_left first second),
        Int.ediv_mul_cancel (Int.gcd_dvd_right first second)]
    _ = 1 * (first.gcd second : ℤ) := by
      simpa only [one_mul] using (Int.gcd_eq_gcd_ab first second).symm

def bezoutBinary (first second : ℤ) : GeneralLinearGroup (Fin 2) ℤ :=
  if nonzero : first.gcd second ≠ 0 then
    ⟨!![first.gcdA second, first.gcdB second;
        -(second / (first.gcd second : ℤ)), first / (first.gcd second : ℤ)],
      !![first / (first.gcd second : ℤ), -first.gcdB second;
        second / (first.gcd second : ℤ), first.gcdA second], by
        have normalized := normalizedBezout first second nonzero
        ext row column
        fin_cases row <;> fin_cases column <;>
          norm_num [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith, by
        have normalized := normalizedBezout first second nonzero
        ext row column
        fin_cases row <;> fin_cases column <;>
          norm_num [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith⟩
  else 1

theorem bezoutBinary_mulVec (first second : ℤ) :
    (bezoutBinary first second).val *ᵥ ![first, second] =
      ![(first.gcd second : ℤ), 0] := by
  by_cases nonzero : first.gcd second ≠ 0
  · have leftDiv := Int.ediv_mul_cancel (Int.gcd_dvd_left first second)
    have rightDiv := Int.ediv_mul_cancel (Int.gcd_dvd_right first second)
    have cross : -(second / (first.gcd second : ℤ)) * first +
        (first / (first.gcd second : ℤ)) * second = 0 := by
      linear_combination (second / (first.gcd second : ℤ)) * leftDiv -
        (first / (first.gcd second : ℤ)) * rightDiv
    simp only [bezoutBinary, dite_eq_left nonzero]
    ext coordinate
    fin_cases coordinate
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm] using
        (Int.gcd_eq_gcd_ab first second).symm
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using cross
  · have bothZero := Int.gcd_eq_zero_iff.mp (not_ne_iff.mp nonzero)
    simp [bezoutBinary, bothZero.1, bothZero.2]

def integralVectorReduction (vector : Fin 3 → ℤ) : IntegralGL3 :=
  planeLevi (bezoutBinary (vector 0) ((vector 1).gcd (vector 2))) 1 *
    lineLevi 1 (bezoutBinary (vector 1) (vector 2))

theorem integralVectorReduction_mulVec (vector : Fin 3 → ℤ) :
    (integralVectorReduction vector).val *ᵥ vector =
      ![((vector 0).gcd ((vector 1).gcd (vector 2)) : ℤ), 0, 0] := by
  have lineReduction :
      (lineLevi (1 : ℤˣ) (bezoutBinary (vector 1) (vector 2))).val *ᵥ vector =
        ![vector 0, ((vector 1).gcd (vector 2) : ℤ), 0] := by
    have binaryReduction := bezoutBinary_mulVec (vector 1) (vector 2)
    ext coordinate
    fin_cases coordinate
    · simp [lineLevi_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · simpa [lineLevi_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two] using congrFun binaryReduction 0
    · simpa [lineLevi_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two] using congrFun binaryReduction 1
  have planeReduction := bezoutBinary_mulVec (vector 0) ((vector 1).gcd (vector 2))
  change ((planeLevi (bezoutBinary (vector 0) ((vector 1).gcd (vector 2))) 1).val *
    (lineLevi (1 : ℤˣ) (bezoutBinary (vector 1) (vector 2))).val) *ᵥ vector = _
  rw [← Matrix.mulVec_mulVec, lineReduction]
  ext coordinate
  fin_cases coordinate
  · simpa [planeLevi, planeBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_two] using congrFun planeReduction 0
  · simpa [planeLevi, planeBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_two] using congrFun planeReduction 1
  · simp [planeLevi, planeBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
