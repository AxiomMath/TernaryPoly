module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.HeckeTrace

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def rationalBinaryRep (degree : ℕ) (twist : ℤ) : Rep ℂ BinaryRationalGL :=
  Rep.of ((Binary.homogeneousAction degree twist).comp (GeneralLinearGroup.map (algebraMap ℚ ℂ)))

theorem rationalBinaryRep_integral (degree : ℕ) (twist : ℤ)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (polynomial : Binary.HomogeneousPoly degree) :
    (rationalBinaryRep degree twist).ρ (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) polynomial =
      (arithmeticBinaryRep degree twist).ρ matrix polynomial := by
  change Binary.homogeneousAction degree twist
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix)) polynomial =
      Binary.homogeneousAction degree twist (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) polynomial
  congr 2

def modularHeckePoint (prime : Nat.Primes) : Option (Fin prime.val) → ℂ → ℂ
  | none, point => (prime.val : ℂ) * point
  | some index, point => (point + (index.val : ℂ)) / (prime.val : ℂ)

theorem modularHeckePoint_upper (prime : Nat.Primes) (index : Option (Fin prime.val)) (point : UpperHalfPlane) :
    ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime index) • point : UpperHalfPlane) : ℂ) =
      modularHeckePoint prime index point := by
  cases index with
  | none => exact binaryHeckeDilate_smul prime.val prime.property.pos point
  | some index => exact binaryHeckeTranslate_smul prime.val prime.property.pos index point

theorem modularHeckePoint_im_pos (prime : Nat.Primes) (index : Option (Fin prime.val))
    (point : ℂ) (positive : 0 < point.im) : 0 < (modularHeckePoint prime index point).im := by
  let upper : UpperHalfPlane := ⟨point, positive⟩
  rw [← modularHeckePoint_upper prime index upper]
  exact (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime index) • upper).im_pos

theorem binaryPointPower_affine_substitution (degree : ℕ) (a b d point : ℂ)
    (a_nonzero : a ≠ 0) (d_nonzero : d ≠ 0) :
    Binary.substitute !![a, b; 0, d] (binaryPointPower degree ((a * point + b) / d)).val =
      (a ^ degree • binaryPointPower degree point).val := by
  have relation := binaryPointPower_mobius_substitution degree d (-b) 0 a ((a * point + b) / d)
    (by simpa using a_nonzero)
  have argument : (d * ((a * point + b) / d) + -b) / a = point := by
    field_simp
    ring
  simpa only [neg_neg, neg_zero, zero_mul, zero_add, argument] using relation

theorem rationalBinaryRep_hecke_inverse_coe (degree : ℕ) (twist : ℤ) (prime : Nat.Primes)
    (index : Option (Fin prime.val)) (polynomial : Binary.HomogeneousPoly degree) :
    ((rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹ polynomial).val =
      (prime.val : ℂ) ^ (-twist) • Binary.substitute
        ((binaryHeckeRepresentative prime index).val.map (algebraMap ℚ ℂ)) polynomial.val := by
  change (Binary.homogeneousAction degree twist
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryHeckeRepresentative prime index)⁻¹) polynomial).val = _
  rw [Binary.homogeneousAction_coe, Binary.action_apply]
  have determinant : Binary.determinantCharacter twist
      (GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryHeckeRepresentative prime index)⁻¹) =
        (prime.val : ℂ) ^ (-twist) := by
    unfold Binary.determinantCharacter
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, map_inv]
    have det_value : (GeneralLinearGroup.det
        (GeneralLinearGroup.map (algebraMap ℚ ℂ) (binaryHeckeRepresentative prime index))).val = prime.val := by
      cases index with
      | none => simp [binaryHeckeRepresentative, binaryHeckeDilate, GeneralLinearGroup.val_det_apply,
          Matrix.det_fin_two]
      | some index => simp [binaryHeckeRepresentative, binaryHeckeTranslate, GeneralLinearGroup.val_det_apply,
          Matrix.det_fin_two]
    rw [det_value]
    exact (zpow_neg (prime.val : ℂ) twist).symm
  rw [determinant, ← map_inv, inv_inv]
  rfl

theorem rationalBinaryRep_hecke_dilate_pointPower (degree : ℕ) (twist : ℤ) (prime : Nat.Primes) (point : ℂ) :
    (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime none)⁻¹
      (binaryPointPower degree (modularHeckePoint prime none point)) =
        ((prime.val : ℂ) ^ (-twist) * (prime.val : ℂ) ^ degree) • binaryPointPower degree point := by
  apply Subtype.ext
  rw [rationalBinaryRep_hecke_inverse_coe]
  have matrix_eq : ((binaryHeckeRepresentative prime none).val.map (algebraMap ℚ ℂ)) =
      !![(prime.val : ℂ), 0; 0, 1] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryHeckeRepresentative, binaryHeckeDilate, Matrix.map]
  rw [matrix_eq]
  have substitution := binaryPointPower_affine_substitution degree (prime.val : ℂ) 0 1 point
    (Nat.cast_ne_zero.mpr prime.property.ne_zero) one_ne_zero
  simp only [add_zero, div_one] at substitution
  change (prime.val : ℂ) ^ (-twist) •
    Binary.substitute !![(prime.val : ℂ), 0; 0, 1] (binaryPointPower degree ((prime.val : ℂ) * point)).val = _
  rw [substitution]
  simp only [Submodule.coe_smul, smul_smul]

theorem rationalBinaryRep_hecke_translate_pointPower (degree : ℕ) (twist : ℤ) (prime : Nat.Primes)
    (index : Fin prime.val) (point : ℂ) :
    (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime (some index))⁻¹
      (binaryPointPower degree (modularHeckePoint prime (some index) point)) =
        (prime.val : ℂ) ^ (-twist) • binaryPointPower degree point := by
  apply Subtype.ext
  rw [rationalBinaryRep_hecke_inverse_coe]
  have matrix_eq : ((binaryHeckeRepresentative prime (some index)).val.map (algebraMap ℚ ℂ)) =
      !![(1 : ℂ), (index.val : ℂ); 0, (prime.val : ℂ)] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryHeckeRepresentative, binaryHeckeTranslate, Matrix.map]
  rw [matrix_eq]
  have substitution := binaryPointPower_affine_substitution degree 1 (index.val : ℂ) (prime.val : ℂ) point
    one_ne_zero (Nat.cast_ne_zero.mpr prime.property.ne_zero)
  simp only [one_mul, one_pow, one_smul] at substitution
  change (prime.val : ℂ) ^ (-twist) •
    Binary.substitute !![(1 : ℂ), (index.val : ℂ); 0, (prime.val : ℂ)]
      (binaryPointPower degree ((point + (index.val : ℂ)) / (prime.val : ℂ))).val = _
  rw [substitution]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
