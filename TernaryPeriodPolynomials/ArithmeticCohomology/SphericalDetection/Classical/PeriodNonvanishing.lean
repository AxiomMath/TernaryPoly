module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodMellin
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Multiplicativity

@[expose] public section


open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem levelOneCuspForm_hecke_LSeries_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (argument : ℝ) (convergent : (weight : ℝ) / 2 + 1 < argument) :
    LSeries (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) (argument : ℂ) ≠ 0 := by
  have large := levelOneCuspForm_weight_ge_twelve form nonzero
  have positive : 0 < weight := by omega
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  obtain ⟨normalized, initial, normalized_relations, normalized_eq⟩ :=
    levelOneCuspForm_hecke_normalize form nonzero eigenvalues relations
  have nonvanishing := cuspForm_removedLSeries_ne_zero_of_recurrence positive normalized 1 argument convergent
    eigenvalues (fun prime => (prime.val : ℂ) ^ (weight - 1))
    (by simpa only [Subgroup.strictWidthInfty_SL2Z] using initial)
    (by simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_multiplicative normalized period eigenvalues normalized_relations initial)
    (fun prime => by simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_coefficient normalized period prime (eigenvalues prime) (normalized_relations prime) initial)
    (fun prime exponent => by simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_power_recurrence normalized period prime (eigenvalues prime) (normalized_relations prime) exponent)
  have removed (coefficients : ℕ → ℂ) : removeEulerCoefficients coefficients 1 = coefficients := by
    funext index
    simp [removeEulerCoefficients]
  rw [removed] at nonvanishing
  simp only [Subgroup.strictWidthInfty_SL2Z] at nonvanishing
  have expansion : UpperHalfPlane.qExpansion 1 normalized =
      ((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • UpperHalfPlane.qExpansion 1 form := by
    rw [normalized_eq]
    change UpperHalfPlane.qExpansion 1
      (((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • (form : UpperHalfPlane → ℂ)) = _
    exact ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1) period _ form
  have coefficients : (fun index => (UpperHalfPlane.qExpansion 1 normalized).coeff index) =
      ((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ •
        (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) := by
    funext index
    rw [expansion, PowerSeries.coeff_smul]
    rfl
  rw [coefficients, LSeries_smul] at nonvanishing
  exact fun zero => nonvanishing (by rw [zero, mul_zero])

/-- Two interior critical moments are nonzero; for even weight their powers have opposite parity. -/
theorem levelOneCuspForm_interiorMoments_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues) :
    cuspImaginaryMoment form (weight - 4).toNat ≠ 0 ∧
      cuspImaginaryMoment form (weight - 3).toNat ≠ 0 := by
  have large := levelOneCuspForm_weight_ge_twelve form nonzero
  have large_real : (12 : ℝ) ≤ weight := by exact_mod_cast large
  have first_index : ((weight - 4).toNat : ℤ) = weight - 4 := Int.toNat_of_nonneg (by omega)
  have second_index : ((weight - 3).toNat : ℤ) = weight - 3 := Int.toNat_of_nonneg (by omega)
  have first_real : ((weight - 4).toNat : ℝ) = (weight : ℝ) - 4 := by exact_mod_cast first_index
  have second_real : ((weight - 3).toNat : ℝ) = (weight : ℝ) - 3 := by exact_mod_cast second_index
  have first_complex : ((weight - 4).toNat : ℂ) + 1 = (((weight : ℝ) - 3 : ℝ) : ℂ) := by
    exact_mod_cast (show ((weight - 4).toNat : ℝ) + 1 = (weight : ℝ) - 3 by rw [first_real]; ring)
  have second_complex : ((weight - 3).toNat : ℂ) + 1 = (((weight : ℝ) - 2 : ℝ) : ℂ) := by
    exact_mod_cast (show ((weight - 3).toNat : ℝ) + 1 = (weight : ℝ) - 2 by rw [second_real]; ring)
  constructor
  · apply cuspImaginaryMoment_ne_zero (by omega) form _ (by rw [first_real]; linarith)
    rw [first_complex]
    exact levelOneCuspForm_hecke_LSeries_ne_zero form nonzero eigenvalues relations _ (by linarith)
  · apply cuspImaginaryMoment_ne_zero (by omega) form _ (by rw [second_real]; linarith)
    rw [second_complex]
    exact levelOneCuspForm_hecke_LSeries_ne_zero form nonzero eigenvalues relations _ (by linarith)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
