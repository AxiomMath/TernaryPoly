module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.MixedCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem arithmeticLevel_mem_iff (matrix : IntegralGL3) :
    matrix ∈ arithmeticLevel ↔
      ∀ column, (matrix.val 2 column : ZMod 3) = if column = 2 then 1 else 0 := by
  change lastRow ᵥ* (reductionThree matrix).val = lastRow ↔ _
  constructor
  · intro row_eq column
    have entry_eq := congrFun row_eq column
    fin_cases column <;>
      simpa [lastRow, reductionThree, Matrix.vecMul, Fin.sum_univ_three,
        GeneralLinearGroup.map_apply] using entry_eq
  · intro entries
    funext column
    have entry_eq := entries column
    fin_cases column <;>
      simpa [lastRow, reductionThree, Matrix.vecMul, Fin.sum_univ_three,
        GeneralLinearGroup.map_apply] using entry_eq

theorem rationalLevel_mem_of_integral (matrix : IntegralGL3)
    (level_mem : matrix ∈ arithmeticLevel) :
    GeneralLinearGroup.map (Int.castRingHom ℚ) matrix ∈ rationalLevel := by
  exact MonoidHom.mem_range.mpr ⟨⟨matrix, level_mem⟩, rfl⟩

theorem rationalLevel_lineUnipotent (first second : ℤ) :
    Adelic.lineUnipotent (first : ℚ) (second : ℚ) ∈ rationalLevel := by
  have integral_mem : Adelic.lineUnipotent first second ∈ arithmeticLevel := by
    rw [arithmeticLevel_mem_iff]
    intro column
    fin_cases column <;> simp [Adelic.lineUnipotent, Adelic.upperUnipotent]
  have image_eq : GeneralLinearGroup.map (Int.castRingHom ℚ)
      (Adelic.lineUnipotent first second) =
        Adelic.lineUnipotent (first : ℚ) (second : ℚ) := by
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [GeneralLinearGroup.map_apply, Adelic.lineUnipotent, Adelic.upperUnipotent]
  rw [← image_eq]
  exact rationalLevel_mem_of_integral _ integral_mem

theorem rationalLevel_badLineLevi (matrix : IntegralGL3)
    (levi_mem : BadLineLevi matrix) :
    GeneralLinearGroup.map (Int.castRingHom ℚ) matrix ∈ rationalLevel :=
  rationalLevel_mem_of_integral matrix levi_mem.1

theorem pureMixed_radical_bar {degree : ℕ}
    (cocycle : cocycles rationalLevel
      (rationalCoefficientComponent degree trivialCharacter))
    (pure : PureMixedBadLine cocycle) (first second third fourth : ℤ) :
    barValue rationalLevel (rationalCoefficientComponent degree trivialCharacter)
      cocycle (Adelic.lineUnipotent (first : ℚ) (second : ℚ))
        (Adelic.lineUnipotent (third : ℚ) (fourth : ℚ)) = 0 :=
  pure.1 first second third fourth

theorem pureMixed_levi_bar {degree : ℕ}
    (cocycle : cocycles rationalLevel
      (rationalCoefficientComponent degree trivialCharacter))
    (pure : PureMixedBadLine cocycle) (first second : IntegralGL3)
    (first_mem : BadLineLevi first) (second_mem : BadLineLevi second) :
    barValue rationalLevel (rationalCoefficientComponent degree trivialCharacter)
      cocycle (GeneralLinearGroup.map (Int.castRingHom ℚ) first)
        (GeneralLinearGroup.map (Int.castRingHom ℚ) second) = 0 := by
  simpa only [barValue, map_mul] using pure.2 first second first_mem second_mem

theorem mixedValue_eq_mixedBarEdge {degree : ℕ}
    (cocycle : cocycles rationalLevel
      (rationalCoefficientComponent degree trivialCharacter))
    (levi radical : RationalGL3) :
    (mixedValue rationalLevel (rationalCoefficientComponent degree trivialCharacter)
      cocycle levi radical).val = mixedBarEdge cocycle levi radical := by
  simp only [mixedValue, barValue, mul_assoc, mul_inv_cancel_left]
  rfl

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
