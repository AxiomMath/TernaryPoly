module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.BinaryPrimitive

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def modularBinaryRep (degree : ℕ) (twist : ℤ) : Rep ℂ (SpecialLinearGroup (Fin 2) ℤ) :=
  Rep.res SpecialLinearGroup.toGL (arithmeticBinaryRep degree twist)

/-- The actual cocycle of the holomorphic primitive, based at `I`. -/
def classicalBinaryCocycle {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    groupCohomology.cocycles₁ (modularBinaryRep degree twist) :=
  ⟨fun matrix => classicalBinaryPrimitive form degree
      ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    have relation := classicalBinaryPrimitive_modular form degree weight_eq twist first
      (SpecialLinearGroup.mapGL ℝ second • UpperHalfPlane.I)
    rw [← mul_smul, ← map_mul] at relation
    exact sub_eq_iff_eq_add.mp relation⟩

theorem classicalBinaryCocycle_apply {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    classicalBinaryCocycle form degree weight_eq twist matrix = classicalBinaryPrimitive form degree
      ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := rfl

theorem classicalBinaryCocycle_S {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    classicalBinaryCocycle form degree weight_eq twist ModularGroup.S = 0 := by
  rw [classicalBinaryCocycle_apply]
  have fixes : SpecialLinearGroup.mapGL ℝ ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
    exact ModularGroup.stabilizer_I.mpr (by simp)
  rw [fixes]
  exact classicalBinaryPrimitive_basepoint form degree

theorem modularBinaryCocycle_S_mem_of_H1_zero (degree : ℕ) (twist : ℤ)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist))
    (translation_zero : cycle ModularGroup.T = 0)
    (class_zero : groupCohomology.H1π (modularBinaryRep degree twist) cycle = 0) :
    cycle ModularGroup.S ∈ binaryEndpointPolynomialSpan degree := by
  obtain ⟨potential, boundary⟩ := (groupCohomology.H1π_eq_zero_iff cycle).mp class_zero
  have values (matrix : SpecialLinearGroup (Fin 2) ℤ) :
      oneBoundaryCycle (arithmeticBinaryRep degree twist) potential (SpecialLinearGroup.toGL matrix) =
        cycle matrix := congrFun boundary matrix
  rw [← values ModularGroup.T] at translation_zero
  rw [← values ModularGroup.S]
  exact arithmeticBinaryBoundary_S_mem_endpointSpan degree twist potential translation_zero

theorem modularBinaryCocycle_H1_ne_zero_of_periodParity {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist))
    (translation_zero : cycle ModularGroup.T = 0)
    (period_value : cycle ModularGroup.S = binaryParityComponent degree parity.val (cuspPeriodPolynomial form degree)) :
    groupCohomology.H1π (modularBinaryRep degree twist) cycle ≠ 0 := by
  intro class_zero
  have member := modularBinaryCocycle_S_mem_of_H1_zero degree twist cycle translation_zero class_zero
  rw [period_value] at member
  obtain ⟨first, second⟩ := levelOneCuspForm_periodParity_nonzero form nonzero eigenvalues relations
    degree weight_eq even
  fin_cases parity
  · exact first member
  · exact second member

end TernaryPeriodPolynomials.SphericalDetection.Helpers
