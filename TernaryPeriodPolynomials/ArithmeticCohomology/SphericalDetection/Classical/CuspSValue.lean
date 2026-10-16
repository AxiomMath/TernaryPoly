module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CuspLimits

@[expose] public section


open GeneralEisenstein Matrix MeasureTheory Filter
open scoped Topology

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem modularS_imaginary (height : ℝ) (positive : 0 < height) :
    ((SpecialLinearGroup.mapGL ℝ ModularGroup.S •
      UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)) : UpperHalfPlane) : ℂ) =
        Complex.I * ((height⁻¹ : ℝ) : ℂ) := by
  let point : UpperHalfPlane := ⟨Complex.I * (height : ℂ), by simpa using positive⟩
  have point_eq : UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)) = point :=
    UpperHalfPlane.ofComplex_apply point
  rw [point_eq]
  change ((ModularGroup.S • point : UpperHalfPlane) : ℂ) = _
  rw [UpperHalfPlane.modular_S_smul]
  change (-(Complex.I * (height : ℂ)))⁻¹ = _
  simp [Complex.inv_I, mul_comm]

theorem classicalBinaryPrimitive_S_imaginary {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ)
    (height : ℝ) (positive : 0 < height) :
    classicalBinaryPrimitive form degree (Complex.I * ((height⁻¹ : ℝ) : ℂ)) =
      (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL ModularGroup.S)
        (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ))) := by
  let point : UpperHalfPlane := ⟨Complex.I * (height : ℂ), by simpa using positive⟩
  have relation := classicalBinaryPrimitive_modular form degree weight_eq twist ModularGroup.S point
  have base : classicalBinaryPrimitive form degree
      ((SpecialLinearGroup.mapGL ℝ ModularGroup.S • UpperHalfPlane.I : UpperHalfPlane) : ℂ) = 0 :=
    classicalBinaryCocycle_S form degree weight_eq twist
  have image : ((SpecialLinearGroup.mapGL ℝ ModularGroup.S • point : UpperHalfPlane) : ℂ) =
      Complex.I * ((height⁻¹ : ℝ) : ℂ) := by
    have point_eq : UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)) = point :=
      UpperHalfPlane.ofComplex_apply point
    simpa only [point_eq] using modularS_imaginary height positive
  rw [base, sub_zero, image] at relation
  exact relation

theorem classicalBinaryCuspConstant_S {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL ModularGroup.S)
        (classicalBinaryCuspConstant form degree) =
      classicalBinaryCuspConstant form degree - cuspPeriodPolynomial form degree := by
  let action : Binary.HomogeneousPoly degree →ₗ[ℂ] Binary.HomogeneousPoly degree :=
    (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL ModularGroup.S)
  apply (binaryStandardBasis degree).ext_elem
  intro position
  let functional := (binaryStandardBasis degree).coord position
  have first := classicalBinaryPrimitive_tendsto_atTop positive form degree (functional.comp action)
  have second := (classicalBinaryPrimitive_tendsto_zero positive form degree functional).comp
    (tendsto_inv_atTop_nhdsGT_zero (𝕜 := ℝ))
  have same : (fun height : ℝ => (functional.comp action)
      (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ)))) =ᶠ[atTop]
      (fun height : ℝ => functional (classicalBinaryPrimitive form degree (Complex.I * ((height⁻¹ : ℝ) : ℂ)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with height height_positive
    exact congrArg functional (classicalBinaryPrimitive_S_imaginary form degree weight_eq twist height height_positive).symm
  have equal := tendsto_nhds_unique (first.congr' same) second
  change functional (action (classicalBinaryCuspConstant form degree)) =
    functional (classicalBinaryCuspConstant form degree - cuspPeriodPolynomial form degree)
  rw [map_sub]
  exact equal

def cuspNormalizedBinaryCocycle {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    groupCohomology.cocycles₁ (modularBinaryRep degree twist) :=
  classicalBinaryCocycle form degree weight_eq twist +
    oneBoundaryCycle (modularBinaryRep degree twist) (classicalBinaryCuspConstant form degree)

theorem cuspNormalizedBinaryCocycle_H1 {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    groupCohomology.H1π (modularBinaryRep degree twist) (cuspNormalizedBinaryCocycle form degree weight_eq twist) =
      groupCohomology.H1π (modularBinaryRep degree twist) (classicalBinaryCocycle form degree weight_eq twist) := by
  rw [cuspNormalizedBinaryCocycle, map_add]
  erw [oneBoundaryCycle_H1_zero]
  rw [add_zero]

theorem cuspNormalizedBinaryCocycle_S {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    cuspNormalizedBinaryCocycle form degree weight_eq twist ModularGroup.S = -cuspPeriodPolynomial form degree := by
  let action : Module.End ℂ (Binary.HomogeneousPoly degree) :=
    (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL ModularGroup.S)
  let value : Binary.HomogeneousPoly degree := classicalBinaryCocycle form degree weight_eq twist ModularGroup.S
  have value_zero : value = 0 := classicalBinaryCocycle_S form degree weight_eq twist
  have reflected : action (classicalBinaryCuspConstant form degree) =
      classicalBinaryCuspConstant form degree - cuspPeriodPolynomial form degree :=
    classicalBinaryCuspConstant_S positive form degree weight_eq twist
  change value + (action (classicalBinaryCuspConstant form degree) - classicalBinaryCuspConstant form degree) = _
  rw [value_zero, zero_add, reflected]
  abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
