module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.EulerProduct

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem levelOneCuspForm_classicalEuler_outerRatio_normalized {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (eigenvalues : Nat.Primes → ℂ) (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (initial : (UpperHalfPlane.qExpansion 1 form).coeff 1 = 1) (modulus : ℕ) :
    HasProd (fun place : {place : Nat.Primes // place.val.Coprime modulus} =>
      classicalPrimeEulerPolynomial place.val.val weight (eigenvalues place.val) ((weight : ℂ) - 1) /
        classicalPrimeEulerPolynomial place.val.val weight (eigenvalues place.val) ((weight : ℂ) - 2))
      (LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) modulus)
          ((weight : ℂ) - 2) /
        LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) modulus)
          ((weight : ℂ) - 1)) := by
  have nonzero : form ≠ 0 := by
    intro zero
    simp [zero, UpperHalfPlane.qExpansion_zero] at initial
  have weight_large := levelOneCuspForm_weight_ge_twelve form nonzero
  have weight_large_real : (12 : ℝ) ≤ weight := by exact_mod_cast weight_large
  have lower := levelOneCuspForm_classicalEuler_hasProd form (by omega) eigenvalues relations initial modulus
    ((weight : ℝ) - 2) (by linarith)
  have upper := levelOneCuspForm_classicalEuler_hasProd form (by omega) eigenvalues relations initial modulus
    ((weight : ℝ) - 1) (by linarith)
  have nonvanishing := levelOneCuspForm_hecke_outerLValues_ne_zero form modulus eigenvalues relations initial
  simpa only [Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_ofNat, Complex.ofReal_one,
    inv_div_inv] using lower.div₀ upper nonvanishing.2

theorem levelOneCuspForm_classicalEuler_outerRatio {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues) (modulus : ℕ) :
    HasProd (fun place : {place : Nat.Primes // place.val.Coprime modulus} =>
      classicalPrimeEulerPolynomial place.val.val weight (eigenvalues place.val) ((weight : ℂ) - 1) /
        classicalPrimeEulerPolynomial place.val.val weight (eigenvalues place.val) ((weight : ℂ) - 2))
      (LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) modulus)
          ((weight : ℂ) - 2) /
        LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) modulus)
          ((weight : ℂ) - 1)) := by
  obtain ⟨normalized, initial, normalized_relations, normalized_eq⟩ :=
    levelOneCuspForm_hecke_normalize form nonzero eigenvalues relations
  have product := levelOneCuspForm_classicalEuler_outerRatio_normalized normalized eigenvalues normalized_relations initial modulus
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  have first_nonzero := cuspForm_hecke_first_coefficient_ne_zero form period nonzero eigenvalues relations
  have expansion : UpperHalfPlane.qExpansion 1 normalized =
      ((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • UpperHalfPlane.qExpansion 1 form := by
    rw [normalized_eq]
    change UpperHalfPlane.qExpansion 1
      (((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • (form : UpperHalfPlane → ℂ)) = _
    exact ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1) period _ form
  have coefficients : removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 normalized).coeff index)
      modulus = ((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ •
        removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) modulus := by
    funext index
    rw [expansion]
    simp only [removeEulerCoefficients, PowerSeries.coeff_smul, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [coefficients, LSeries_smul, LSeries_smul,
    mul_div_mul_left _ _ (inv_ne_zero first_nonzero)] at product
  exact product

theorem levelOneCuspForm_classicalEuler_outerRatio_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues) (modulus : ℕ) :
    (∏' place : {place : Nat.Primes // place.val.Coprime modulus},
      classicalPrimeEulerPolynomial place.val.val weight (eigenvalues place.val) ((weight : ℂ) - 1) /
        classicalPrimeEulerPolynomial place.val.val weight (eigenvalues place.val) ((weight : ℂ) - 2)) ≠ 0 := by
  rw [(levelOneCuspForm_classicalEuler_outerRatio form nonzero eigenvalues relations modulus).tprod_eq]
  have values := levelOneCuspForm_hecke_outerLValues_ne_zero_of_nonzero form nonzero modulus eigenvalues relations
  simp only [Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_ofNat, Complex.ofReal_one] at values
  exact div_ne_zero values.1 values.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
