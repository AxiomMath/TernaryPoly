module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.IntegralFlags

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def binarySwitch : GeneralLinearGroup (Fin 2) ℤ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by decide, by decide⟩

def binaryRowMatrix (first second : ℤ) (square : first * first = 1) :
    GeneralLinearGroup (Fin 2) ℤ :=
  ⟨!![-second, first; first, 0], !![0, first; first, second], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, square, mul_comm], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, square, mul_comm]⟩

def binaryNegativeSecond : GeneralLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by decide, by decide⟩

theorem binaryRowCorrection (first second : ZMod 3)
    (nonzero : first ≠ 0 ∨ second ≠ 0) :
    ∃ binary : GeneralLinearGroup (Fin 2) ℤ,
      first * (binary.val 0 0 : ZMod 3) + second * (binary.val 1 0 : ZMod 3) = 0 ∧
      first * (binary.val 0 1 : ZMod 3) + second * (binary.val 1 1 : ZMod 3) = 1 := by
  fin_cases first <;> fin_cases second
  · exact False.elim (nonzero.elim
      (fun impossible => impossible rfl) (fun impossible => impossible rfl))
  · exact ⟨1, by decide⟩
  · exact ⟨binaryNegativeSecond, by decide⟩
  · exact ⟨binarySwitch, by decide⟩
  · exact ⟨binaryRowMatrix 1 1 rfl, by decide⟩
  · exact ⟨binaryRowMatrix 1 (-1) rfl, by decide⟩
  · exact ⟨binaryRowMatrix (-1) 0 rfl, by decide⟩
  · exact ⟨binaryRowMatrix (-1) 1 rfl, by decide⟩
  · exact ⟨binaryRowMatrix (-1) (-1) rfl, by decide⟩

theorem integralLineRepresentative_bad_first_entry (integral : IntegralGL3)
    (bad : ¬ GoodFlag .line (QuotientGroup.mk (integralRational integral))) :
    (integral.val 2 0 : ZMod 3) = 0 := by
  by_contra nonzero
  apply bad
  refine ⟨fun row => integral.val row 0, ?_, nonzero⟩
  refine ⟨integralRational integral, rfl, ![1, 0, 0], ⟨rfl, rfl⟩, ?_⟩
  ext row
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    mul_one, mul_zero, add_zero]
  rfl

theorem integralLastRow_nonzero (integral : IntegralGL3)
    (firstZero : (integral.val 2 0 : ZMod 3) = 0) :
    (integral.val 2 1 : ZMod 3) ≠ 0 ∨ (integral.val 2 2 : ZMod 3) ≠ 0 := by
  by_contra vanishing
  push Not at vanishing
  have inverseEntry := congrArg
    (fun matrix : Matrix (Fin 3) (Fin 3) (ZMod 3) => matrix 2 2)
    (reductionThree integral).mul_inv
  change ((reductionThree integral).val *
    ((reductionThree integral)⁻¹).val) 2 2 = 1 at inverseEntry
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at inverseEntry
  change (integral.val 2 0 : ZMod 3) * _ +
    (integral.val 2 1 : ZMod 3) * _ +
    (integral.val 2 2 : ZMod 3) * _ = 1 at inverseEntry
  simp only [firstZero, vanishing.1, vanishing.2, zero_mul, add_zero] at inverseEntry
  exact zero_ne_one inverseEntry

theorem badLine_has_arithmetic_representative (flag : Flags .line)
    (bad : ¬ GoodFlag .line flag) :
    ∃ element : arithmeticLevel, QuotientGroup.mk (rationalInclusion element) = flag := by
  obtain ⟨integral, represented⟩ := rationalLine_has_integral_representative flag
  have firstZero : (integral.val 2 0 : ZMod 3) = 0 :=
    integralLineRepresentative_bad_first_entry integral (by rw [represented]; exact bad)
  obtain ⟨binary, firstCorrection, secondCorrection⟩ := binaryRowCorrection
    (integral.val 2 1 : ZMod 3) (integral.val 2 2 : ZMod 3)
    (integralLastRow_nonzero integral firstZero)
  let corrected := integral * lineLevi (1 : ℤˣ) binary
  have correctedLevel : corrected ∈ arithmeticLevel := by
    change lastRow ᵥ* (reductionThree corrected).val = lastRow
    funext column
    simp only [lastRow, single_vecMul, one_smul]
    change (corrected.val 2 column : ZMod 3) = _
    dsimp [corrected]
    rw [lineLevi_val]
    fin_cases column
    · simpa [Matrix.mul_apply, Fin.sum_univ_three] using firstZero
    · simpa [Matrix.mul_apply, Fin.sum_univ_three]
        using firstCorrection
    · simpa [Matrix.mul_apply, Fin.sum_univ_three]
        using secondCorrection
  refine ⟨⟨corrected, correctedLevel⟩, ?_⟩
  rw [← represented]
  apply QuotientGroup.eq.mpr
  change (integralRational corrected)⁻¹ * integralRational integral ∈ lineParabolic ℚ
  dsimp [corrected]
  rw [map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
  exact (lineParabolic ℚ).inv_mem
    (inLine_map (Int.castRingHom ℚ) (lineLevi (1 : ℤˣ) binary)
      (lineLevi_mem (1 : ℤˣ) binary))

theorem badLine_is_standardBadLine_orbit (flag : Flags .line)
    (bad : ¬ GoodFlag .line flag) :
    ∃ element : rationalLevel, element.val • standardBadLine = flag := by
  obtain ⟨integral, represented⟩ := badLine_has_arithmetic_representative flag bad
  refine ⟨⟨rationalInclusion integral, ⟨integral, rfl⟩⟩, ?_⟩
  change QuotientGroup.mk (rationalInclusion integral * 1) = flag
  simpa only [mul_one] using represented

theorem badLine_iff_standardBadLine_orbit (flag : Flags .line) :
    ¬ GoodFlag .line flag ↔
      ∃ element : rationalLevel, element.val • standardBadLine = flag := by
  constructor
  · exact badLine_is_standardBadLine_orbit flag
  · rintro ⟨element, transported⟩ good
    have standardGood := (goodFlag_rationalLevel_smul_iff .line element standardBadLine).mp
      (transported.symm ▸ good)
    exact standardBadLine_not_good standardGood

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
