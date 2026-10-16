module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Upper.CuspRadicalPrimitive
public import TernaryPeriodPolynomials.Building.BoundaryApartments.CyclicCrossed

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix

def integralUpperTranslation (integer : ℤ) : IntegralGL3 :=
  ⟨!![1,0,0;0,1,integer;0,0,1], !![1,0,0;0,1,-integer;0,0,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]⟩

theorem integralUpperTranslation_arithmetic (integer : ℤ) :
    integralUpperTranslation integer ∈ arithmeticLevel := by
  change lastRow ᵥ* (reductionThree (integralUpperTranslation integer)).val = lastRow
  ext index
  fin_cases index <;>
    simp [lastRow, reductionThree, integralUpperTranslation, Matrix.single_vecMul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

def upperTranslationPower (integer : ℤ) : rationalLevel :=
  integralImage (integralUpperTranslation integer) (integralUpperTranslation_arithmetic integer)

theorem upperTranslationPower_entries (integer : ℤ) :
    (upperTranslationPower integer).val.val = !![1,0,0;0,1,(integer : ℚ);0,0,1] ∧
    (upperTranslationPower integer).val.inv = !![1,0,0;0,1,-(integer : ℚ);0,0,1] := by
  have entries : (upperTranslationPower integer).val.val =
      !![1,0,0;0,1,(integer : ℚ);0,0,1] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [upperTranslationPower, integralImage, integralUpperTranslation,
        GeneralLinearGroup.map_apply]
  refine ⟨entries, ?_⟩
  apply Matrix.left_inv_eq_left_inv (A := (upperTranslationPower integer).val.val)
    (upperTranslationPower integer).val.inv_mul
  rw [entries]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem upperTranslationPower_add (first second : ℤ) :
    upperTranslationPower (first + second) = upperTranslationPower first *
      upperTranslationPower second := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  rw [Subgroup.coe_mul, GeneralLinearGroup.coe_mul,
    (upperTranslationPower_entries (first + second)).1,
    (upperTranslationPower_entries first).1, (upperTranslationPower_entries second).1]
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, add_comm]

def upperTranslationPowerHom : Multiplicative ℤ →* rationalLevel where
  toFun integer := upperTranslationPower integer.toAdd
  map_one' := by
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro row column
    change (upperTranslationPower 0).val.val row column = (1 : RationalGL3).val row column
    rw [(upperTranslationPower_entries 0).1]
    fin_cases row <;> fin_cases column <;> rfl
  map_mul' first second := upperTranslationPower_add first.toAdd second.toAdd

theorem upperTranslationPower_one : upperTranslationPower 1 = upperCuspTranslation := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  rw [(upperTranslationPower_entries 1).1, upperCuspTranslation_entries.1]
  rfl

theorem upperTranslationPower_eq_zpow (integer : ℤ) :
    upperTranslationPower integer = upperCuspTranslation ^ integer := by
  have power := MonoidHom.apply_mint rationalLevel upperTranslationPowerHom
    (Multiplicative.ofAdd integer)
  change upperTranslationPower integer = upperTranslationPower 1 ^ integer at power
  rw [upperTranslationPower_one] at power
  exact power

theorem upperTranslationPower_line (integer : ℤ) :
    (upperTranslationPower integer).val ∈ Adelic.lineParabolic ℚ := by
  constructor <;> rw [(upperTranslationPower_entries integer).1] <;> rfl

theorem upperTranslationPower_block (integer : ℤ) :
    (upperTranslationPower integer).val.val 0 1 = 0 ∧
      (upperTranslationPower integer).val.val 0 2 = 0 := by
  rw [(upperTranslationPower_entries integer).1]
  exact ⟨rfl, rfl⟩

theorem upperTranslationPower_radical_conjugate (integer left right : ℤ) :
    (upperTranslationPower integer)⁻¹ * integralRadical left right *
        upperTranslationPower integer = integralRadical left (integer * left + right) := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, GeneralLinearGroup.coe_mul, integralRadical_val]
  change ((upperTranslationPower integer).val.inv *
      (Adelic.lineUnipotent (left : ℚ) (right : ℚ)).val *
      (upperTranslationPower integer).val.val) row column = _
  rw [(upperTranslationPower_entries integer).2, (upperTranslationPower_entries integer).1]
  fin_cases row <;> fin_cases column <;>
    simp [Adelic.lineUnipotent, Adelic.upperUnipotent, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, mul_comm]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
