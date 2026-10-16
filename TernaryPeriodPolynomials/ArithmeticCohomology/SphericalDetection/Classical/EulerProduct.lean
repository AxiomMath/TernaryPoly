module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Euler.ProductConvergence
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.ClassicalEulerScaling
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Multiplicativity

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem levelOneCuspForm_classicalEuler_hasProd {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (weight_positive : 0 < weight) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (initial : (UpperHalfPlane.qExpansion 1 form).coeff 1 = 1)
    (modulus : ℕ) (argument : ℝ) (argument_bound : (weight : ℝ) / 2 + 1 < argument) :
    HasProd (fun place : {place : Nat.Primes // place.val.Coprime modulus} =>
      (classicalPrimeEulerPolynomial place.val.val weight (eigenvalues place.val) argument)⁻¹)
      (LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) modulus) argument) := by
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  have first := fun prime => cuspForm_hecke_prime_coefficient form period prime (eigenvalues prime) (relations prime) initial
  have recurrence := fun prime exponent => cuspForm_hecke_prime_power_recurrence form period prime (eigenvalues prime)
    (relations prime) exponent
  have multiplicative := cuspForm_hecke_multiplicative form period eigenvalues relations initial
  obtain ⟨first_root, second_root, root_sum, root_product, first_bound, second_bound⟩ :=
    cuspForm_eulerRoots form eigenvalues (fun prime => (prime.val : ℂ) ^ (weight - 1))
      (by simpa only [Subgroup.strictWidthInfty_SL2Z] using initial)
      (by simpa only [Subgroup.strictWidthInfty_SL2Z] using first)
      (by simpa only [Subgroup.strictWidthInfty_SL2Z] using recurrence)
  have polynomial (prime : Nat.Primes) :
      (1 - first_root prime * (prime.val : ℂ) ^ (-(argument : ℂ))) *
          (1 - second_root prime * (prime.val : ℂ) ^ (-(argument : ℂ))) =
        classicalPrimeEulerPolynomial prime.val weight (eigenvalues prime) argument := by
    rw [classicalPrimeEulerPolynomial, ← root_sum prime, ← root_product prime]
    ring
  have multipliable := outerEulerProduct_restricted_multipliable first_root second_root (weight : ℝ) argument
    (fun prime => prime.val.Coprime modulus) first_bound second_bound argument_bound
  simp_rw [scaledEulerRoot_eq_cpow, polynomial] at multipliable
  have summable := cuspForm_LSeries_norm_summable weight_positive form argument (by simpa using argument_bound)
  simp only [Subgroup.strictWidthInfty_SL2Z] at summable
  have identity := quadraticEulerSeries_removeFactors_eq_product
    (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) modulus argument eigenvalues
    (fun prime => (prime.val : ℂ) ^ (weight - 1)) first_root second_root initial multiplicative first recurrence
    root_sum root_product summable
  simp_rw [polynomial] at identity
  rw [identity]
  exact multipliable.hasProd

end TernaryPeriodPolynomials.SphericalDetection.Helpers
