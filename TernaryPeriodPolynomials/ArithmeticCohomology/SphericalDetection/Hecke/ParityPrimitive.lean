module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.ReflectionCoefficient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def classicalReflectedHeckePrimitive {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (twist : ℤ) (prime : Nat.Primes) (point : ℂ) : Binary.HomogeneousPoly degree :=
  let action : Option (Fin prime.val) → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    fun index => (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
  ∑ index : Option (Fin prime.val), action index (binaryParityReflection degree
    (classicalBinaryPrimitive form degree (binaryComplexReflection (modularHeckePoint prime index point))))

theorem classicalReflectedHeckePrimitive_sub {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) (even : Even degree)
    (prime : Nat.Primes) (first second : ℂ) (first_positive : 0 < first.im) (second_positive : 0 < second.im) :
    classicalReflectedHeckePrimitive form degree twist prime first -
      classicalReflectedHeckePrimitive form degree twist prime second =
        binaryParityReflection degree
          (classicalHeckePrimitive form degree twist prime (binaryComplexReflection first) -
            classicalHeckePrimitive form degree twist prime (binaryComplexReflection second)) := by
  let action : Option (Fin prime.val) → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    fun index => (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
  let left (index : Option (Fin prime.val)) (point : ℂ) := action index (binaryParityReflection degree
    (classicalBinaryPrimitive form degree (binaryComplexReflection (modularHeckePoint prime index point))))
  let right (index : Option (Fin prime.val)) (point : ℂ) := action index
    (classicalBinaryPrimitive form degree (modularHeckePoint prime index (binaryComplexReflection point)))
  have summand (index : Option (Fin prime.val)) :
      left index first - left index second = binaryParityReflection degree
        (right (heckeReflectionPermutation prime index) first - right (heckeReflectionPermutation prime index) second) := by
    let u : UpperHalfPlane :=
      ⟨modularHeckePoint prime (heckeReflectionPermutation prime index) (binaryComplexReflection first),
        modularHeckePoint_im_pos prime _ _ (by rw [binaryComplexReflection_im]; exact first_positive)⟩
    let v : UpperHalfPlane :=
      ⟨modularHeckePoint prime (heckeReflectionPermutation prime index) (binaryComplexReflection second),
        modularHeckePoint_im_pos prime _ _ (by rw [binaryComplexReflection_im]; exact second_positive)⟩
    have u_eq : UpperHalfPlane.ofComplex
        (modularHeckePoint prime (heckeReflectionPermutation prime index) (binaryComplexReflection first)) = u :=
      UpperHalfPlane.ofComplex_apply u
    have v_eq : UpperHalfPlane.ofComplex
        (modularHeckePoint prime (heckeReflectionPermutation prime index) (binaryComplexReflection second)) = v :=
      UpperHalfPlane.ofComplex_apply v
    have u_image := heckeReflection_upper prime index first first_positive
    have v_image := heckeReflection_upper prime index second second_positive
    rw [u_eq] at u_image
    rw [v_eq] at v_image
    have relation := classicalBinaryPrimitive_modular_sub form degree weight_eq twist (heckeReflectionTranslation prime index) u v
    rw [← u_image, ← v_image] at relation
    dsimp only [left, right]
    rw [← map_sub, ← map_sub, relation]
    exact (heckeReflection_coefficient degree twist even prime index
      (classicalBinaryPrimitive form degree u - classicalBinaryPrimitive form degree v)).trans
        (congrArg (binaryParityReflection degree) (map_sub (action (heckeReflectionPermutation prime index)) _ _))
  change (∑ index, left index first) - (∑ index, left index second) =
    binaryParityReflection degree ((∑ index, right index first) - (∑ index, right index second))
  rw [← Finset.sum_sub_distrib]
  simp_rw [summand]
  exact (Equiv.sum_comp (heckeReflectionPermutation prime)
    (fun index => binaryParityReflection degree (right index first - right index second))).trans
      ((map_sum (binaryParityReflection degree) (fun index => right index first - right index second) Finset.univ).symm.trans
        (congrArg (binaryParityReflection degree)
          (Finset.sum_sub_distrib (fun index => right index first) (fun index => right index second))))

def classicalHeckeParityPrimitive {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (twist : ℤ) (parity : ℕ) (prime : Nat.Primes) (point : ℂ) : Binary.HomogeneousPoly degree :=
  let action : Option (Fin prime.val) → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    fun index => (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
  ∑ index : Option (Fin prime.val), action index (classicalParityPrimitive form degree parity (modularHeckePoint prime index point))

theorem classicalHeckeParityPrimitive_eq {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (twist : ℤ) (parity : ℕ) (prime : Nat.Primes) (point : ℂ) :
    classicalHeckeParityPrimitive form degree twist parity prime point =
      (2 : ℂ)⁻¹ • (classicalHeckePrimitive form degree twist prime point +
        (-1 : ℂ) ^ parity • classicalReflectedHeckePrimitive form degree twist prime point) := by
  let action : Option (Fin prime.val) → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    fun index => (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
  let first (index : Option (Fin prime.val)) := classicalBinaryPrimitive form degree (modularHeckePoint prime index point)
  let second (index : Option (Fin prime.val)) := binaryParityReflection degree
    (classicalBinaryPrimitive form degree (binaryComplexReflection (modularHeckePoint prime index point)))
  change (∑ index, action index ((2 : ℂ)⁻¹ • (first index + (-1 : ℂ) ^ parity • second index))) =
    (2 : ℂ)⁻¹ • ((∑ index, action index (first index)) + (-1 : ℂ) ^ parity • ∑ index, action index (second index))
  simp only [map_smul, map_add, ← Finset.smul_sum, Finset.sum_add_distrib]

theorem classicalHeckeParityPrimitive_eq_trace {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (twist : ℤ) (parity : ℕ) (prime : Nat.Primes) (point : UpperHalfPlane) :
    classicalHeckeParityPrimitive form degree twist parity prime point =
      modularHeckeTrace (rationalBinaryRep degree twist) prime
        (fun point => classicalParityPrimitive form degree parity point) point := by
  let action : Option (Fin prime.val) → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    fun index => (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
  change (∑ index : Option (Fin prime.val), action index (classicalParityPrimitive form degree parity
    (modularHeckePoint prime index point))) = ∑ index : Option (Fin prime.val), action index
      (classicalParityPrimitive form degree parity
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime index) • point : UpperHalfPlane) : ℂ))
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg (fun argument : ℂ => action index (classicalParityPrimitive form degree parity argument))
    (modularHeckePoint_upper prime index point).symm

theorem classicalHeckeParityPrimitive_comparison (halfWeight : ℤ)
    (form target : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (degree : ℕ) (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (prime : Nat.Primes)
    (transformed : (target : UpperHalfPlane → ℂ) = scalarPrimeHecke halfWeight prime form)
    (point : ℂ) (positive : 0 < point.im) :
    classicalHeckeParityPrimitive form degree twist parity prime point -
      classicalHeckeParityPrimitive form degree twist parity prime Complex.I =
        (prime.val : ℂ) ^ (-halfWeight - 1 - twist) • classicalParityPrimitive target degree parity point := by
  have reflected_positive : 0 < (binaryComplexReflection point).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have reflected := classicalReflectedHeckePrimitive_sub form degree weight_eq twist even prime point Complex.I positive (by simp)
  rw [binaryComplexReflection_basepoint] at reflected
  have first := classicalHeckePrimitive_comparison halfWeight form target degree weight_eq twist prime transformed point positive
  have second := classicalHeckePrimitive_comparison halfWeight form target degree weight_eq twist prime transformed
    (binaryComplexReflection point) reflected_positive
  rw [classicalHeckeParityPrimitive_eq, classicalHeckeParityPrimitive_eq]
  have rearrange (a b c d : Binary.HomogeneousPoly degree) :
      (2 : ℂ)⁻¹ • (a + (-1 : ℂ) ^ parity • b) - (2 : ℂ)⁻¹ • (c + (-1 : ℂ) ^ parity • d) =
        (2 : ℂ)⁻¹ • ((a - c) + (-1 : ℂ) ^ parity • (b - d)) := by module
  rw [rearrange, first, reflected, second, map_smul]
  dsimp only [classicalParityPrimitive]
  module

end TernaryPeriodPolynomials.SphericalDetection.Helpers
