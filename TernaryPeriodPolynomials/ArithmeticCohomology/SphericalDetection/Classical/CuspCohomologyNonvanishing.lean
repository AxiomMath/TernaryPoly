module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CuspTValue

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspPeriodPolynomial_not_mem_endpointSpan {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) :
    cuspPeriodPolynomial form degree ∉ binaryEndpointPolynomialSpan degree := by
  have large := levelOneCuspForm_weight_ge_twelve form nonzero
  have degree_large : 10 ≤ degree := by omega
  have moment := (levelOneCuspForm_interiorMoments_ne_zero form nonzero eigenvalues relations).1
  rw [show (weight - 4).toNat = degree - 2 by omega] at moment
  let position : Fin (degree + 1) := ⟨2, by omega⟩
  have left : position ≠ 0 := by intro equal; have := congrArg Fin.val equal; simp [position] at this
  have right : position ≠ Fin.last degree := by
    intro equal
    have := congrArg Fin.val equal
    change 2 = degree at this
    omega
  intro member
  have zero := binaryEndpointPolynomialSpan_coord_zero degree _ member position left right
  exact cuspPeriodPolynomial_coord_ne_zero form degree position moment zero

theorem cuspNormalizedBinaryCocycle_H1_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    groupCohomology.H1π (modularBinaryRep degree twist)
      (cuspNormalizedBinaryCocycle form degree weight_eq twist) ≠ 0 := by
  have positive : 0 < weight := by omega
  intro class_zero
  have member := modularBinaryCocycle_S_mem_of_H1_zero degree twist
    (cuspNormalizedBinaryCocycle form degree weight_eq twist)
    (cuspNormalizedBinaryCocycle_T positive form degree weight_eq twist) class_zero
  rw [cuspNormalizedBinaryCocycle_S positive form degree weight_eq twist] at member
  apply cuspPeriodPolynomial_not_mem_endpointSpan form nonzero eigenvalues relations degree weight_eq
  simpa only [neg_neg] using (binaryEndpointPolynomialSpan degree).neg_mem member

/-- The arithmetic cohomology class constructed from the holomorphic primitive is nonzero. -/
theorem classicalBinaryCocycle_H1_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    groupCohomology.H1π (modularBinaryRep degree twist)
      (classicalBinaryCocycle form degree weight_eq twist) ≠ 0 := by
  rw [← cuspNormalizedBinaryCocycle_H1 form degree weight_eq twist]
  exact cuspNormalizedBinaryCocycle_H1_ne_zero form nonzero eigenvalues relations degree weight_eq twist

end TernaryPeriodPolynomials.SphericalDetection.Helpers
