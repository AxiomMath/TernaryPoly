module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityBoundary

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem modularCocycleParity_idempotent (degree : ℕ) (twist : ℤ) (parity : ℕ)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) :
    modularCocycleParity degree twist parity (modularCocycleParity degree twist parity cycle) =
      modularCocycleParity degree twist parity cycle := by
  change (2 : ℂ)⁻¹ • (modularCocycleParity degree twist parity cycle + (-1 : ℂ) ^ parity •
    modularCocycleReflection degree twist (modularCocycleParity degree twist parity cycle)) = _
  rw [modularCocycleParity_reflection, smul_smul, ← pow_add,
    (show Even (parity + parity) from ⟨parity, rfl⟩).neg_one_pow, one_smul]
  module

theorem arithmeticParityCocycle_parity (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) :
    arithmeticParityCocycle degree twist even parity sign
      (modularCocycleParity degree twist parity cycle) =
        arithmeticParityCocycle degree twist even parity sign cycle := by
  apply groupCohomology.cocycles₁_ext
  intro matrix
  change modularCocycleParity degree twist parity (modularCocycleParity degree twist parity cycle)
    (splitRadicalCoordinate integralDeterminantSplitting matrix) = _
  rw [modularCocycleParity_idempotent]
  rfl

theorem arithmeticParityCocycle_H1_zero_iff (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) :
    groupCohomology.H1π (arithmeticBinaryRep degree twist)
      (arithmeticParityCocycle degree twist even parity sign cycle) = 0 ↔
    groupCohomology.H1π (modularBinaryRep degree twist)
      (modularCocycleParity degree twist parity cycle) = 0 := by
  constructor
  · intro zero
    by_contra nonzero
    exact arithmeticParityCocycle_H1_ne_zero degree twist even parity sign cycle nonzero zero
  · intro zero
    obtain ⟨potential, boundary⟩ := (groupCohomology.H1π_eq_zero_iff _).mp zero
    have cycle_eq : oneBoundaryCycle (modularBinaryRep degree twist) potential =
        modularCocycleParity degree twist parity cycle := by
      apply groupCohomology.cocycles₁_ext
      intro matrix
      exact congrFun boundary matrix
    rw [← arithmeticParityCocycle_parity degree twist even parity sign cycle,
      ← cycle_eq, arithmeticParityCocycle_boundary degree twist even parity sign potential]
    exact oneBoundaryCycle_H1_zero _ _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
