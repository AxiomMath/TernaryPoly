module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Parabolic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlagRows

theorem lastRow_ne_zero {coefficientRing : Type*} [CommRing coefficientRing]
    [Nontrivial coefficientRing] (matrix : GL3 coefficientRing) :
    (fun column : Fin 3 => matrix.val 2 column) ≠ 0 := by
  intro zeroRow
  have rowEntry (column : Fin 3) : matrix.val 2 column = 0 := congrFun zeroRow column
  have identityEntry := congrArg
    (fun value : Matrix (Fin 3) (Fin 3) coefficientRing => value 2 2) matrix.mul_inv
  simp [Matrix.mul_apply, rowEntry] at identityEntry

theorem lastRow_planeParabolic_mul {coefficientRing : Type*} [CommRing coefficientRing]
    (parabolicElement : planeParabolic coefficientRing) (matrix : GL3 coefficientRing)
    (column : Fin 3) :
    (parabolicElement.val * matrix).val 2 column =
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement).val * matrix.val 2 column := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three,
    parabolicElement.property.1, parabolicElement.property.2,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit]

theorem planeFlag_eq_iff_rows (first second : RationalGL3) :
    (QuotientGroup.mk first : Flags .plane) = QuotientGroup.mk second ↔
      ∃ scalar : ℚˣ, ∀ column : Fin 3,
        (first⁻¹).val 2 column = scalar.val * (second⁻¹).val 2 column := by
  rw [QuotientGroup.eq]
  constructor
  · intro parabolicMembership
    let parabolicElement : planeParabolic ℚ := ⟨first⁻¹ * second, parabolicMembership⟩
    refine ⟨TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic.planeCornerUnit parabolicElement, fun column => ?_⟩
    have rowProduct := lastRow_planeParabolic_mul parabolicElement second⁻¹ column
    change ((first⁻¹ * second) * second⁻¹).val 2 column = _ at rowProduct
    simpa only [mul_inv_cancel_right] using rowProduct
  · rintro ⟨scalar, rowsEquality⟩
    have rowProduct (column : Fin 3) :
        (first⁻¹ * second).val 2 column = scalar.val * (second⁻¹ * second).val 2 column := by
      simp only [Units.val_mul, Matrix.mul_apply, rowsEquality, Finset.mul_sum, mul_assoc]
    constructor
    · simpa only [inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
        Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 0), mul_zero] using rowProduct 0
    · simpa only [inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
        Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 1), mul_zero] using rowProduct 1

theorem flag_eq_of_representative_rows {first second : Flags .plane}
    (scalar : ℚˣ)
    (rowsEquality : ∀ column : Fin 3,
      (first.out⁻¹).val 2 column = scalar.val * (second.out⁻¹).val 2 column) :
    first = second := by
  have representativeEquality := (planeFlag_eq_iff_rows first.out second.out).mpr
    ⟨scalar, rowsEquality⟩
  simpa only [QuotientGroup.mk, Quotient.out_eq] using representativeEquality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlagRows
