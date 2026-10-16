module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RemovedEulerFactors

@[expose] public section


open Matrix

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspForm_removedLSeries_ne_zero_of_recurrence {weight : ℤ}
    {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} [level.IsArithmetic]
    (weight_positive : 0 < weight) (form : CuspForm level weight)
    (modulus : ℕ) (argument : ℝ) (argument_bound : (weight : ℝ) / 2 + 1 < argument)
    (trace determinant : Nat.Primes → ℂ)
    (initial : (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff 1 = 1)
    (multiplicative : ∀ first_index second_index : ℕ,
      first_index.Coprime second_index →
        (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
            (first_index * second_index) =
          (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff first_index *
            (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff second_index)
    (first : ∀ place : Nat.Primes,
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff place.val = trace place)
    (recurrence : ∀ (place : Nat.Primes) (exponent : ℕ),
      (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ (exponent + 2)) =
        trace place * (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ (exponent + 1)) -
        determinant place * (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ exponent)) :
    LSeries (removeEulerCoefficients
      (fun index => (UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff index)
      modulus) (argument : ℂ) ≠ 0 := by
  obtain ⟨first_root, second_root, root_sum, root_product, first_bound, second_bound⟩ :=
    cuspForm_eulerRoots form trace determinant initial first recurrence
  exact quadraticEulerSeries_removeFactors_ne_zero _ modulus (weight : ℝ) argument
    trace determinant first_root second_root initial multiplicative first recurrence
    root_sum root_product
    (cuspForm_LSeries_norm_summable weight_positive form argument (by
      simpa only [Complex.ofReal_re] using argument_bound))
    first_bound second_bound argument_bound

/-- The small-weight exclusion and Euler nonvanishing for the actual incomplete series. -/
theorem levelOneCuspForm_removedOuterLValues_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (modulus : ℕ) (trace determinant : Nat.Primes → ℂ)
    (initial : (UpperHalfPlane.qExpansion
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
      form).coeff 1 = 1)
    (multiplicative : ∀ first_index second_index : ℕ,
      first_index.Coprime second_index →
        (UpperHalfPlane.qExpansion
          (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
          form).coeff (first_index * second_index) =
        (UpperHalfPlane.qExpansion
          (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
          form).coeff first_index *
        (UpperHalfPlane.qExpansion
          (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
          form).coeff second_index)
    (first : ∀ place : Nat.Primes,
      (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff place.val = trace place)
    (recurrence : ∀ (place : Nat.Primes) (exponent : ℕ),
      (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff (place.val ^ (exponent + 2)) =
      trace place * (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff (place.val ^ (exponent + 1)) -
      determinant place * (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff (place.val ^ exponent)) :
    LSeries (removeEulerCoefficients
      (fun index => (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff index) modulus) (((weight : ℝ) - 2 : ℝ) : ℂ) ≠ 0 ∧
    LSeries (removeEulerCoefficients
      (fun index => (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff index) modulus) (((weight : ℝ) - 1 : ℝ) : ℂ) ≠ 0 := by
  have nonzero : form ≠ 0 := by
    intro zero
    simp [zero, UpperHalfPlane.qExpansion_zero] at initial
  have weight_large := levelOneCuspForm_weight_ge_twelve form nonzero
  have weight_positive : 0 < weight := by omega
  have weight_large_real : (12 : ℝ) ≤ weight := by exact_mod_cast weight_large
  constructor
  · exact cuspForm_removedLSeries_ne_zero_of_recurrence weight_positive form modulus
      ((weight : ℝ) - 2) (by linarith) trace determinant initial multiplicative first recurrence
  · exact cuspForm_removedLSeries_ne_zero_of_recurrence weight_positive form modulus
      ((weight : ℝ) - 1) (by linarith) trace determinant initial multiplicative first recurrence

end TernaryPeriodPolynomials.SphericalDetection.Helpers
