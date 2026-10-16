module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.SphereIndices

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryLowerCarry_isUnit {R : Type*} [CommRing R] (prime offset digit quotient : R)
    (relation : prime * quotient + offset * digit = 1) : IsUnit (!![prime, offset; -digit, quotient] : Matrix (Fin 2) (Fin 2) R) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have determinant : (!![prime, offset; -digit, quotient] : Matrix (Fin 2) (Fin 2) R).det = 1 := by
    rw [Matrix.det_fin_two]
    change prime * quotient - offset * (-digit) = 1
    rw [mul_neg, sub_neg_eq_add]
    exact relation
  rw [determinant]
  exact isUnit_one

def binaryLowerCarryCompact {R : Type*} [CommRing R] (prime offset digit quotient : R)
    (relation : prime * quotient + offset * digit = 1) : GeneralLinearGroup (Fin 2) R :=
  (binaryLowerCarry_isUnit prime offset digit quotient relation).unit

theorem binaryLowerCarryCompact_val {R : Type*} [CommRing R] (prime offset digit quotient : R)
    (relation : prime * quotient + offset * digit = 1) :
    (binaryLowerCarryCompact prime offset digit quotient relation).val = !![prime, offset; -digit, quotient] :=
  (binaryLowerCarry_isUnit prime offset digit quotient relation).unit_spec

theorem binaryLowerCarryCompact_map {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S)
    (prime offset digit quotient : R) (relation : prime * quotient + offset * digit = 1)
    (mapped_relation : hom prime * hom quotient + hom offset * hom digit = 1) :
    GeneralLinearGroup.map hom (binaryLowerCarryCompact prime offset digit quotient relation) =
      binaryLowerCarryCompact (hom prime) (hom offset) (hom digit) (hom quotient) mapped_relation := by
  apply Units.ext
  funext row column
  rw [GeneralLinearGroup.map_apply, binaryLowerCarryCompact_val, binaryLowerCarryCompact_val]
  fin_cases row <;> fin_cases column <;> simp

theorem binaryLowerPivot_upper_carry {R : Type*} [CommRing R] (prime scale : Rˣ) (base offset digit quotient : R)
    (relation : prime.val * quotient + offset * digit = 1) :
    binaryLowerPivot scale base * binaryUpperPivot prime offset =
      binaryLowerPivot (prime * scale) (base + scale.val * digit) *
        binaryLowerCarryCompact prime.val offset digit quotient relation := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, binaryLowerCarryCompact_val]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryLowerPivot, binaryUpperPivot, Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · linear_combination -scale.val * relation

end TernaryPeriodPolynomials.SphericalDetection.Helpers
