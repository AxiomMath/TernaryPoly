module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.ReflectionCorrespondence

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem heckeReflection_inverse_rational (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    (binaryHeckeRepresentative prime index)⁻¹ * binaryRationalReflection *
        GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL (heckeReflectionTranslation prime index)) =
      binaryRationalReflection * (binaryHeckeRepresentative prime (heckeReflectionPermutation prime index))⁻¹ := by
  have inverse := congrArg Inv.inv (heckeReflection_rational prime index)
  simp only [_root_.mul_inv_rev, binaryRationalReflection_inverse] at inverse
  rw [inverse]
  simp [mul_assoc]

theorem heckeReflection_coefficient (degree : ℕ) (twist : ℤ) (even : Even degree)
    (prime : Nat.Primes) (index : Option (Fin prime.val)) (polynomial : Binary.HomogeneousPoly degree) :
    (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
      (binaryParityReflection degree
        ((arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL (heckeReflectionTranslation prime index)) polynomial)) =
      binaryParityReflection degree ((rationalBinaryRep degree twist).ρ
        (binaryHeckeRepresentative prime (heckeReflectionPermutation prime index))⁻¹ polynomial) := by
  let action : BinaryRationalGL → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    (rationalBinaryRep degree twist).ρ
  have multiplication (first second : BinaryRationalGL) (polynomial : Binary.HomogeneousPoly degree) :
      action (first * second) polynomial = action first (action second polynomial) :=
    congrArg (fun linear : Module.End ℂ (Binary.HomogeneousPoly degree) => linear polynomial)
      ((rationalBinaryRep degree twist).ρ.map_mul first second)
  have reflection (polynomial : Binary.HomogeneousPoly degree) :
      action binaryRationalReflection polynomial = (-1 : ℂ) ^ twist • binaryParityReflection degree polynomial :=
    rationalBinaryRep_reflection degree twist even polynomial
  have relation := congrArg (fun matrix : BinaryRationalGL => action matrix polynomial)
    (heckeReflection_inverse_rational prime index)
  rw [multiplication, multiplication, multiplication, reflection, reflection, map_smul] at relation
  have integral : action (GeneralLinearGroup.map (Int.castRingHom ℚ)
      (SpecialLinearGroup.toGL (heckeReflectionTranslation prime index))) polynomial =
      (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL (heckeReflectionTranslation prime index)) polynomial :=
    rationalBinaryRep_integral degree twist _ polynomial
  rw [integral] at relation
  exact smul_right_injective (Binary.HomogeneousPoly degree)
    (zpow_ne_zero twist (by norm_num : (-1 : ℂ) ≠ 0)) relation

theorem classicalBinaryPrimitive_modular_sub {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (first second : UpperHalfPlane) :
    classicalBinaryPrimitive form degree ((SpecialLinearGroup.mapGL ℝ matrix • first : UpperHalfPlane) : ℂ) -
      classicalBinaryPrimitive form degree ((SpecialLinearGroup.mapGL ℝ matrix • second : UpperHalfPlane) : ℂ) =
        (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL matrix)
          (classicalBinaryPrimitive form degree first - classicalBinaryPrimitive form degree second) := by
  let action : Module.End ℂ (Binary.HomogeneousPoly degree) :=
    (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL matrix)
  let a := classicalBinaryPrimitive form degree ((SpecialLinearGroup.mapGL ℝ matrix • first : UpperHalfPlane) : ℂ)
  let b := classicalBinaryPrimitive form degree ((SpecialLinearGroup.mapGL ℝ matrix • second : UpperHalfPlane) : ℂ)
  let c := classicalBinaryPrimitive form degree ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ)
  have left : a - c = action (classicalBinaryPrimitive form degree first) :=
    classicalBinaryPrimitive_modular form degree weight_eq twist matrix first
  have right : b - c = action (classicalBinaryPrimitive form degree second) :=
    classicalBinaryPrimitive_modular form degree weight_eq twist matrix second
  change @Eq (Binary.HomogeneousPoly degree) (a - b)
    (action (classicalBinaryPrimitive form degree first - classicalBinaryPrimitive form degree second))
  rw [map_sub, ← left, ← right]
  abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
