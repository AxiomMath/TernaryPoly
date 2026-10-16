module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.HeckeLocalization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryPivotReflection {R : Type*} [CommRing R] : GeneralLinearGroup (Fin 2) R :=
  binaryUpperPivot (-1) 0

theorem binaryPivotReflection_square {R : Type*} [CommRing R] :
    (binaryPivotReflection : GeneralLinearGroup (Fin 2) R) * binaryPivotReflection = 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryPivotReflection, binaryUpperPivot, Matrix.mul_apply, Fin.sum_univ_two]

theorem binaryPivotReflection_map {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S) :
    GeneralLinearGroup.map hom binaryPivotReflection = binaryPivotReflection := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryPivotReflection, binaryUpperPivot, GeneralLinearGroup.map_apply]

def padicPrimeForwardRepresentative {prime : ℕ} [Fact prime.Prime] :
    Option (Fin prime) → GeneralLinearGroup (Fin 2) ℚ_[prime]
  | none => binaryLowerPivot (padicPrimePowerUnit 1) 0
  | some index => binaryUpperPivot (padicPrimePowerUnit 1) (index.val : ℚ_[prime])

theorem padicPrimitive_one_sum {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) :
    (∑ index : Fin (prime ^ 1) ⊕ {index : Fin (prime ^ 1) // prime ∣ index.val},
      value (padicPrimitiveRepresentative 1 index)) =
      ∑ index : Option (Fin prime), value (padicPrimeForwardRepresentative index) := by
  classical
  let zero_index : {index : Fin (prime ^ 1) // prime ∣ index.val} :=
    ⟨⟨0, by simpa only [pow_one] using (Nat.Prime.pos Fact.out)⟩, dvd_zero _⟩
  let : Unique {index : Fin (prime ^ 1) // prime ∣ index.val} :=
    { default := zero_index
      uniq := fun index => by
        apply Subtype.ext
        apply Fin.ext
        exact Nat.eq_zero_of_dvd_of_lt index.property (by simpa only [pow_one] using index.val.isLt) }
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_unique,
    padicPrimitiveRepresentative, padicPrimeForwardRepresentative, padicUpperPrimitiveRepresentative,
    padicLowerPrimitiveRepresentative]
  have upper : (∑ index : Fin (prime ^ 1), value (binaryUpperPivot (padicPrimePowerUnit 1) (index.val : ℚ_[prime]))) =
      ∑ index : Fin prime, value (binaryUpperPivot (padicPrimePowerUnit 1) (index.val : ℚ_[prime])) :=
    Equiv.sum_comp (finCongr (pow_one prime))
      (fun index : Fin prime => value (binaryUpperPivot (padicPrimePowerUnit 1) (index.val : ℚ_[prime])))
  rw [upper]
  exact add_comm _ _

theorem padicPrimeForwardRepresentative_mul_hecke {prime : ℕ} [Fact prime.Prime] (index : Option (Fin prime)) :
    padicPrimeForwardRepresentative index * binaryPivotReflection * padicHeckeRepresentative index =
      binaryPivotReflection * GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) := by
  apply Units.ext
  funext row column
  cases index <;> fin_cases row <;> fin_cases column <;>
    simp [padicPrimeForwardRepresentative, padicHeckeRepresentative, binaryHeckeRepresentative,
      binaryHeckeDilate, binaryHeckeTranslate, binaryPivotReflection, binaryUpperPivot, binaryLowerPivot,
      padicPrimePowerUnit, GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.natCast_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem padicPrimeForwardRepresentative_inverse_hecke {prime : ℕ} [Fact prime.Prime] (index : Option (Fin prime)) :
    padicPrimeForwardRepresentative index =
      binaryPivotReflection * GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
        (padicHeckeRepresentative index)⁻¹ * binaryPivotReflection := by
  have product := padicPrimeForwardRepresentative_mul_hecke index
  calc
    _ = (padicPrimeForwardRepresentative index * binaryPivotReflection * padicHeckeRepresentative index) *
        (padicHeckeRepresentative index)⁻¹ * binaryPivotReflection := by
      rw [mul_inv_cancel_right, mul_assoc, binaryPivotReflection_square, mul_one]
    _ = _ := congrArg (fun matrix : GeneralLinearGroup (Fin 2) ℚ_[prime] =>
      matrix * (padicHeckeRepresentative index)⁻¹ * binaryPivotReflection) product

end TernaryPeriodPolynomials.SphericalDetection.Helpers
