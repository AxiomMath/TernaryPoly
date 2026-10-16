module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityCocycle

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryParityComponent_reflection (degree parity : ℕ) (polynomial : Binary.HomogeneousPoly degree) :
    binaryParityReflection degree (binaryParityComponent degree parity polynomial) =
      (-1 : ℂ) ^ parity • binaryParityComponent degree parity polynomial := by
  change binaryParityReflection degree
    ((2 : ℂ)⁻¹ • (polynomial + (-1 : ℂ) ^ parity • binaryParityReflection degree polynomial)) =
      (-1 : ℂ) ^ parity • ((2 : ℂ)⁻¹ • (polynomial + (-1 : ℂ) ^ parity • binaryParityReflection degree polynomial))
  rw [map_smul, map_add, map_smul, binaryParityReflection_involutive degree polynomial]
  have square : (-1 : ℂ) ^ parity * (-1 : ℂ) ^ parity = 1 := by
    rw [← pow_add]
    exact (show Even (parity + parity) from ⟨parity, rfl⟩).neg_one_pow
  rw [smul_comm ((-1 : ℂ) ^ parity) ((2 : ℂ)⁻¹)]
  congr 1
  rw [smul_add, smul_smul, square, one_smul, add_comm]

theorem binaryParityComponent_section_fixed (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (polynomial : Binary.HomogeneousPoly degree) (unit : ℤˣ) :
    (arithmeticBinaryRep degree twist).ρ (integralDeterminantSection unit)
      (binaryParityComponent degree parity polynomial) = binaryParityComponent degree parity polynomial := by
  rcases Int.units_eq_one_or unit with rfl | rfl
  · rw [map_one, map_one]
    rfl
  · rw [arithmeticBinaryRep_section_neg_one degree twist even, sign,
      binaryParityComponent_reflection, smul_smul, ← pow_add]
    rw [(show Even (parity + parity) from ⟨parity, rfl⟩).neg_one_pow, one_smul]

theorem arithmeticParityCocycle_add (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (first second : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) :
    arithmeticParityCocycle degree twist even parity sign (first + second) =
      arithmeticParityCocycle degree twist even parity sign first +
        arithmeticParityCocycle degree twist even parity sign second := by
  apply groupCohomology.cocycles₁_ext
  intro matrix
  change modularCocycleParity degree twist parity (first + second)
    (splitRadicalCoordinate integralDeterminantSplitting matrix) = _
  rw [map_add]
  rfl

theorem arithmeticParityCocycle_boundary (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (polynomial : Binary.HomogeneousPoly degree) :
    arithmeticParityCocycle degree twist even parity sign
      (oneBoundaryCycle (modularBinaryRep degree twist) polynomial) =
        oneBoundaryCycle (arithmeticBinaryRep degree twist) (binaryParityComponent degree parity polynomial) := by
  apply groupCohomology.cocycles₁_ext
  intro matrix
  obtain ⟨special, unit, rfl⟩ := split_exists_pair integralDeterminantSplitting matrix
  change modularCocycleParity degree twist parity (oneBoundaryCycle (modularBinaryRep degree twist) polynomial)
    (splitRadicalCoordinate integralDeterminantSplitting
      (integralDeterminantExtension.inl special * integralDeterminantSplitting unit)) = _
  rw [splitRadicalCoordinate_pair, modularCocycleParity_boundary]
  let action : GeneralLinearGroup (Fin 2) ℤ → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    (arithmeticBinaryRep degree twist).ρ
  let potential := binaryParityComponent degree parity polynomial
  have product : action (SpecialLinearGroup.toGL special * integralDeterminantSection unit) potential =
      action (SpecialLinearGroup.toGL special) (action (integralDeterminantSection unit) potential) :=
    congrArg (fun linear : Module.End ℂ (Binary.HomogeneousPoly degree) => linear potential)
      ((arithmeticBinaryRep degree twist).ρ.map_mul _ _)
  have fixed : action (integralDeterminantSection unit) potential = potential :=
    binaryParityComponent_section_fixed degree twist even parity sign polynomial unit
  change action (SpecialLinearGroup.toGL special) potential - potential =
    action (SpecialLinearGroup.toGL special * integralDeterminantSection unit) potential - potential
  rw [product, fixed]

def classicalArithmeticCocycle {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep degree twist) :=
  arithmeticParityCocycle degree twist even parity sign (classicalBinaryCocycle form degree weight_eq twist)

theorem cuspNormalizedArithmeticCocycle_eq_add_boundary {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    cuspNormalizedArithmeticCocycle form degree weight_eq even twist parity sign =
      classicalArithmeticCocycle form degree weight_eq even twist parity sign +
        oneBoundaryCycle (arithmeticBinaryRep degree twist)
          (binaryParityComponent degree parity (classicalBinaryCuspConstant form degree)) := by
  rw [cuspNormalizedArithmeticCocycle, cuspNormalizedBinaryCocycle,
    arithmeticParityCocycle_add, arithmeticParityCocycle_boundary]
  rfl

theorem cuspNormalizedArithmeticCocycle_H1 {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    groupCohomology.H1π (arithmeticBinaryRep degree twist)
      (cuspNormalizedArithmeticCocycle form degree weight_eq even twist parity sign) =
    groupCohomology.H1π (arithmeticBinaryRep degree twist)
      (classicalArithmeticCocycle form degree weight_eq even twist parity sign) := by
  rw [cuspNormalizedArithmeticCocycle_eq_add_boundary, map_add]
  erw [oneBoundaryCycle_H1_zero]
  rw [add_zero]

theorem classicalArithmeticCocycle_H1_ne_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity.val) :
    groupCohomology.H1π (arithmeticBinaryRep degree twist)
      (classicalArithmeticCocycle form degree weight_eq even twist parity.val sign) ≠ 0 := by
  rw [← cuspNormalizedArithmeticCocycle_H1 form degree weight_eq even twist parity.val sign]
  exact cuspNormalizedArithmeticCocycle_H1_ne_zero form nonzero eigenvalues relations degree weight_eq even
    twist parity sign

end TernaryPeriodPolynomials.SphericalDetection.Helpers
