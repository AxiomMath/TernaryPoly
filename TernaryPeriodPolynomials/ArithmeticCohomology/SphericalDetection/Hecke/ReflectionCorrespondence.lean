module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.ParityPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance heckeReflectionNeZero (prime : Nat.Primes) : NeZero prime.val := ⟨prime.property.ne_zero⟩

def heckeReflectionPermutation (prime : Nat.Primes) : Equiv.Perm (Option (Fin prime.val)) :=
  Equiv.optionCongr (Equiv.neg (Fin prime.val))

def heckeReflectionShift (prime : Nat.Primes) : Option (Fin prime.val) → ℤ
  | none => 0
  | some index => if index = 0 then 0 else -1

def heckeReflectionTranslation (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, heckeReflectionShift prime index; 0, 1], by simp [Matrix.det_fin_two]⟩

def binaryRationalReflection : BinaryRationalGL :=
  GeneralLinearGroup.map (Int.castRingHom ℚ) (integralDeterminantSection (-1))

theorem binaryRationalReflection_inverse : binaryRationalReflection⁻¹ = binaryRationalReflection := by
  rw [binaryRationalReflection, ← map_inv, ← map_inv, inv_neg_one]

theorem heckeReflectionShift_index (prime : Nat.Primes) (index : Fin prime.val) :
    (index.val : ℤ) + ((-index).val : ℤ) = -heckeReflectionShift prime (some index) * prime.val := by
  by_cases zero : index = 0
  · simp [zero, heckeReflectionShift]
  · rw [Fin.val_neg, ite_eq_right zero]
    simp only [heckeReflectionShift, ite_eq_right zero, neg_neg, one_mul]
    have bound := index.isLt
    omega

theorem heckeReflection_rational (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    binaryRationalReflection * binaryHeckeRepresentative prime index =
      GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL (heckeReflectionTranslation prime index)) *
        binaryHeckeRepresentative prime (heckeReflectionPermutation prime index) * binaryRationalReflection := by
  apply Units.ext
  cases index with
  | none =>
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryRationalReflection, integralDeterminantSection, binaryHeckeRepresentative, binaryHeckeDilate,
        heckeReflectionTranslation, heckeReflectionShift, heckeReflectionPermutation, SpecialLinearGroup.toGL,
        Matrix.mul_apply, Fin.sum_univ_two]
  | some index =>
    have indices : (index.val : ℚ) + ((-index).val : ℚ) =
        -(heckeReflectionShift prime (some index) : ℚ) * prime.val := by
      exact_mod_cast heckeReflectionShift_index prime index
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryRationalReflection, integralDeterminantSection, binaryHeckeRepresentative, binaryHeckeTranslate,
        heckeReflectionTranslation, heckeReflectionPermutation, SpecialLinearGroup.toGL,
        Matrix.mul_apply, Fin.sum_univ_two]
    linarith

theorem rationalBinaryRep_reflection (degree : ℕ) (twist : ℤ) (even : Even degree)
    (polynomial : Binary.HomogeneousPoly degree) :
    (rationalBinaryRep degree twist).ρ binaryRationalReflection polynomial =
      (-1 : ℂ) ^ twist • binaryParityReflection degree polynomial := by
  rw [binaryRationalReflection, rationalBinaryRep_integral]
  exact arithmeticBinaryRep_section_neg_one degree twist even polynomial

theorem heckeReflection_upper (prime : Nat.Primes) (index : Option (Fin prime.val))
    (point : ℂ) (positive : 0 < point.im) :
    binaryComplexReflection (modularHeckePoint prime index point) =
      ((SpecialLinearGroup.mapGL ℝ (heckeReflectionTranslation prime index) •
        UpperHalfPlane.ofComplex (modularHeckePoint prime (heckeReflectionPermutation prime index)
          (binaryComplexReflection point)) : UpperHalfPlane) : ℂ) := by
  let argument : UpperHalfPlane :=
    ⟨modularHeckePoint prime (heckeReflectionPermutation prime index) (binaryComplexReflection point),
      modularHeckePoint_im_pos prime _ _ (by rw [binaryComplexReflection_im]; exact positive)⟩
  have argument_eq : UpperHalfPlane.ofComplex
      (modularHeckePoint prime (heckeReflectionPermutation prime index) (binaryComplexReflection point)) = argument :=
    UpperHalfPlane.ofComplex_apply argument
  have translation (argument : UpperHalfPlane) :
      ((SpecialLinearGroup.mapGL ℝ (heckeReflectionTranslation prime index) • argument : UpperHalfPlane) : ℂ) =
        (argument : ℂ) + (heckeReflectionShift prime index : ℂ) := by
    rw [UpperHalfPlane.coe_smul_of_det_pos (by simp)]
    have matrix_eq : (SpecialLinearGroup.mapGL ℝ (heckeReflectionTranslation prime index)).val =
        !![(1 : ℝ), (heckeReflectionShift prime index : ℝ); 0, 1] := by
      change (Int.castRingHom ℝ).mapMatrix !![(1 : ℤ), heckeReflectionShift prime index; 0, 1] = _
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, matrix_eq]
  rw [argument_eq, translation]
  cases index with
  | none =>
    simp [heckeReflectionShift, heckeReflectionPermutation, argument,
      modularHeckePoint, binaryComplexReflection]
  | some index =>
    have indices : (index.val : ℂ) + ((-index).val : ℂ) =
        -(heckeReflectionShift prime (some index) : ℂ) * prime.val := by
      exact_mod_cast heckeReflectionShift_index prime index
    have nonzero : (prime.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr prime.property.ne_zero
    simp [heckeReflectionPermutation, argument,
      modularHeckePoint, binaryComplexReflection]
    field_simp
    linear_combination -indices

end TernaryPeriodPolynomials.SphericalDetection.Helpers
