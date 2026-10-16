module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.ParityPrimitive

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem integralDeterminantSection_upper_basepoint (unit : ℤˣ) :
    GeneralLinearGroup.map (Int.castRingHom ℝ) (integralDeterminantSection unit) • UpperHalfPlane.I =
      UpperHalfPlane.I := by
  rcases Int.units_eq_one_or unit with rfl | rfl
  · rw [map_one, map_one, one_smul]
  · have reflection : GeneralLinearGroup.map (Int.castRingHom ℝ) (integralDeterminantSection (-1)) =
        UpperHalfPlane.J := by
      apply Units.ext
      ext row column
      fin_cases row <;> fin_cases column <;>
        norm_num [GeneralLinearGroup.map_apply, integralDeterminantSection, UpperHalfPlane.val_J]
    rw [reflection]
    apply UpperHalfPlane.ext
    simp [UpperHalfPlane.coe_J_smul]

theorem classicalArithmeticCocycle_apply {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    classicalArithmeticCocycle form degree weight_eq even twist parity sign matrix =
      classicalParityPrimitive form degree parity
        ((GeneralLinearGroup.map (Int.castRingHom ℝ) matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
  obtain ⟨special, unit, rfl⟩ := split_exists_pair integralDeterminantSplitting matrix
  change modularCocycleParity degree twist parity (classicalBinaryCocycle form degree weight_eq twist)
      (splitRadicalCoordinate integralDeterminantSplitting
        (integralDeterminantExtension.inl special * integralDeterminantSplitting unit)) = _
  rw [splitRadicalCoordinate_pair]
  change _ = classicalParityPrimitive form degree parity
    ((GeneralLinearGroup.map (Int.castRingHom ℝ)
      (SpecialLinearGroup.toGL special * integralDeterminantSection unit) • UpperHalfPlane.I : UpperHalfPlane) : ℂ)
  rw [map_mul, mul_smul, integralDeterminantSection_upper_basepoint]
  exact (classicalParityPrimitive_cocycle form degree weight_eq twist parity special).symm

theorem classicalArithmeticCocycle_H1_zero_iff_primitive {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    groupCohomology.H1π (arithmeticBinaryRep degree twist)
      (classicalArithmeticCocycle form degree weight_eq even twist parity sign) = 0 ↔
    ∃ potential : Binary.HomogeneousPoly degree, ∀ matrix : GeneralLinearGroup (Fin 2) ℤ,
      classicalParityPrimitive form degree parity
        ((GeneralLinearGroup.map (Int.castRingHom ℝ) matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
          (let action : Module.End ℂ (Binary.HomogeneousPoly degree) := (arithmeticBinaryRep degree twist).ρ matrix
           action potential - potential) := by
  rw [groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨potential, boundary⟩
    refine ⟨potential, fun matrix => ?_⟩
    exact (classicalArithmeticCocycle_apply form degree weight_eq even twist parity sign matrix).symm.trans
      (congrFun boundary matrix).symm
  · rintro ⟨potential, boundary⟩
    refine ⟨potential, funext fun matrix => ?_⟩
    exact (boundary matrix).symm.trans
      (classicalArithmeticCocycle_apply form degree weight_eq even twist parity sign matrix).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
