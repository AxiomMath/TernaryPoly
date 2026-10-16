module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.CocycleReflection

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem modularCocycleParity_determinant_invariant (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist))
    (unit : ℤˣ) (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    modularCocycleParity degree twist parity cycle (integralDeterminantSplitting.conjAct unit matrix) =
      (arithmeticBinaryRep degree twist).ρ (integralDeterminantSplitting unit)
        (modularCocycleParity degree twist parity cycle matrix) := by
  rcases Int.units_eq_one_or unit with rfl | rfl
  · simp only [map_one, MulAut.one_apply]
    rfl
  · rw [integralDeterminant_conj_neg_one, modularCocycleParity_conj]
    exact (congrArg (fun scalar : ℂ => scalar • binaryParityReflection degree
      (modularCocycleParity degree twist parity cycle matrix)) sign.symm).trans
        (arithmeticBinaryRep_section_neg_one degree twist even _).symm

/-- Extend the determinant-compatible parity cocycle from SL2(Z) to GL2(Z). -/
def arithmeticParityCocycle (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep degree twist) :=
  splitInvariantOneCocycle integralDeterminantSplitting (arithmeticBinaryRep degree twist)
    (modularCocycleParity degree twist parity cycle)
    (modularCocycleParity_determinant_invariant degree twist even parity sign cycle)

theorem arithmeticParityCocycle_specialLinear (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist))
    (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    arithmeticParityCocycle degree twist even parity sign cycle (SpecialLinearGroup.toGL matrix) =
      modularCocycleParity degree twist parity cycle matrix :=
  splitInvariantOneCocycle_inl integralDeterminantSplitting (arithmeticBinaryRep degree twist) _ _ matrix

theorem arithmeticParityCocycle_section (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) (unit : ℤˣ) :
    arithmeticParityCocycle degree twist even parity sign cycle (integralDeterminantSection unit) = 0 :=
  splitInvariantOneCocycle_splitting integralDeterminantSplitting (arithmeticBinaryRep degree twist) _ _ unit

theorem arithmeticParityCocycle_H1_ne_zero (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist))
    (nonzero : groupCohomology.H1π (modularBinaryRep degree twist)
      (modularCocycleParity degree twist parity cycle) ≠ 0) :
    groupCohomology.H1π (arithmeticBinaryRep degree twist)
      (arithmeticParityCocycle degree twist even parity sign cycle) ≠ 0 :=
  splitInvariantOneCocycle_H1_ne_zero integralDeterminantSplitting (arithmeticBinaryRep degree twist) _ _ nonzero

def cuspNormalizedArithmeticCocycle {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep degree twist) :=
  arithmeticParityCocycle degree twist even parity sign (cuspNormalizedBinaryCocycle form degree weight_eq twist)

theorem cuspNormalizedArithmeticCocycle_T {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    cuspNormalizedArithmeticCocycle form degree weight_eq even twist parity sign
      (SpecialLinearGroup.toGL ModularGroup.T) = 0 := by
  rw [cuspNormalizedArithmeticCocycle, arithmeticParityCocycle_specialLinear]
  exact modularCocycleParity_T degree twist parity _
    (cuspNormalizedBinaryCocycle_T positive form degree weight_eq twist)

theorem cuspNormalizedArithmeticCocycle_S {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    cuspNormalizedArithmeticCocycle form degree weight_eq even twist parity sign
      (SpecialLinearGroup.toGL ModularGroup.S) =
        -binaryParityComponent degree parity (cuspPeriodPolynomial form degree) := by
  rw [cuspNormalizedArithmeticCocycle, arithmeticParityCocycle_specialLinear]
  exact cuspNormalizedBinaryCocycle_parity_S positive form degree weight_eq even twist parity

theorem cuspNormalizedArithmeticCocycle_H1_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity.val) :
    groupCohomology.H1π (arithmeticBinaryRep degree twist)
      (cuspNormalizedArithmeticCocycle form degree weight_eq even twist parity.val sign) ≠ 0 :=
  arithmeticParityCocycle_H1_ne_zero degree twist even parity.val sign _
    (cuspNormalizedBinaryCocycle_parity_H1_ne_zero form nonzero eigenvalues relations
      degree weight_eq even twist parity)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
