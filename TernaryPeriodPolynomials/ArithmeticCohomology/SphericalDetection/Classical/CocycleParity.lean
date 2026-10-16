module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.CocycleCentral

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspNormalizedBinaryCocycle_parity_S {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) :
    modularCocycleParity degree twist parity (cuspNormalizedBinaryCocycle form degree weight_eq twist)
      ModularGroup.S = -binaryParityComponent degree parity (cuspPeriodPolynomial form degree) := by
  rw [modularCocycleParity_S degree twist parity _ (modularCocycle_S_inverse degree twist even _),
    cuspNormalizedBinaryCocycle_S positive form degree weight_eq twist, map_neg]

theorem cuspNormalizedBinaryCocycle_parity_H1_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2) :
    groupCohomology.H1π (modularBinaryRep degree twist)
      (modularCocycleParity degree twist parity.val
        (cuspNormalizedBinaryCocycle form degree weight_eq twist)) ≠ 0 := by
  have positive : 0 < weight := by omega
  intro class_zero
  have member := modularBinaryCocycle_S_mem_of_H1_zero degree twist _
    (modularCocycleParity_T degree twist parity.val _
      (cuspNormalizedBinaryCocycle_T positive form degree weight_eq twist)) class_zero
  rw [cuspNormalizedBinaryCocycle_parity_S positive form degree weight_eq even twist parity.val] at member
  have member' := (binaryEndpointPolynomialSpan degree).neg_mem member
  rw [neg_neg] at member'
  obtain ⟨first, second⟩ := levelOneCuspForm_periodParity_nonzero form nonzero eigenvalues relations
    degree weight_eq even
  fin_cases parity
  · exact first member'
  · exact second member'

theorem cuspNormalizedBinaryCocycle_parity_H1 {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) (parity : ℕ) :
    groupCohomology.H1π (modularBinaryRep degree twist)
      (modularCocycleParity degree twist parity (cuspNormalizedBinaryCocycle form degree weight_eq twist)) =
    groupCohomology.H1π (modularBinaryRep degree twist)
      (modularCocycleParity degree twist parity (classicalBinaryCocycle form degree weight_eq twist)) := by
  rw [cuspNormalizedBinaryCocycle, map_add, modularCocycleParity_boundary, map_add]
  erw [oneBoundaryCycle_H1_zero]
  rw [add_zero]

theorem classicalBinaryCocycle_parity_H1_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2) :
    groupCohomology.H1π (modularBinaryRep degree twist)
      (modularCocycleParity degree twist parity.val
        (classicalBinaryCocycle form degree weight_eq twist)) ≠ 0 := by
  rw [← cuspNormalizedBinaryCocycle_parity_H1 form degree weight_eq twist parity.val]
  exact cuspNormalizedBinaryCocycle_parity_H1_ne_zero form nonzero eigenvalues relations
    degree weight_eq even twist parity

end TernaryPeriodPolynomials.SphericalDetection.Helpers
