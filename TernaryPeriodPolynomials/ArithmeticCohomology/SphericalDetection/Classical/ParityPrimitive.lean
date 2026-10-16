module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.HeckePrimitiveComparison

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem modularReflection_upper (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane) :
    binaryComplexReflection ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ) =
      ((SpecialLinearGroup.mapGL ℝ (modularReflection matrix) •
        UpperHalfPlane.ofComplex (binaryComplexReflection point) : UpperHalfPlane) : ℂ) := by
  let reflected : UpperHalfPlane := ⟨binaryComplexReflection point, by
    rw [binaryComplexReflection_im]
    exact point.im_pos⟩
  have reflected_eq : UpperHalfPlane.ofComplex (binaryComplexReflection point) = reflected :=
    UpperHalfPlane.ofComplex_apply reflected
  rw [reflected_eq]
  have determinant (element : SpecialLinearGroup (Fin 2) ℤ) :
      0 < ((GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ element) : ℝˣ) : ℝ) := by simp
  rw [UpperHalfPlane.coe_smul_of_det_pos (determinant matrix),
    UpperHalfPlane.coe_smul_of_det_pos (determinant (modularReflection matrix))]
  simp [binaryComplexReflection, UpperHalfPlane.num, UpperHalfPlane.denom,
    SpecialLinearGroup.mapGL, modularReflection_apply, reflected]
  ring

def classicalParityPrimitive {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree parity : ℕ) (point : ℂ) : Binary.HomogeneousPoly degree :=
  (2 : ℂ)⁻¹ • (classicalBinaryPrimitive form degree point + (-1 : ℂ) ^ parity •
    binaryParityReflection degree (classicalBinaryPrimitive form degree (binaryComplexReflection point)))

theorem classicalParityPrimitive_basepoint {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree parity : ℕ) : classicalParityPrimitive form degree parity Complex.I = 0 := by
  simp only [classicalParityPrimitive, binaryComplexReflection_basepoint, classicalBinaryPrimitive_basepoint,
    map_zero, smul_zero, add_zero]

theorem classicalParityPrimitive_cocycle {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) (parity : ℕ)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    classicalParityPrimitive form degree parity
        ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      modularCocycleParity degree twist parity (classicalBinaryCocycle form degree weight_eq twist) matrix := by
  have reflection := modularReflection_upper matrix UpperHalfPlane.I
  have base : UpperHalfPlane.ofComplex (binaryComplexReflection (UpperHalfPlane.I : ℂ)) = UpperHalfPlane.I := by
    change UpperHalfPlane.ofComplex (binaryComplexReflection Complex.I) = UpperHalfPlane.I
    rw [binaryComplexReflection_basepoint]
    exact UpperHalfPlane.ofComplex_apply UpperHalfPlane.I
  rw [base] at reflection
  rw [classicalParityPrimitive, reflection, modularCocycleParity_apply]
  rfl

theorem classicalParityPrimitive_modular {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) (parity : ℕ)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane) :
    classicalParityPrimitive form degree parity ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ) -
      classicalParityPrimitive form degree parity ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
        (modularBinaryRep degree twist).ρ matrix (classicalParityPrimitive form degree parity point) := by
  let action : Module.End ℂ (Binary.HomogeneousPoly degree) := (modularBinaryRep degree twist).ρ matrix
  let reflected : UpperHalfPlane := ⟨binaryComplexReflection point, by
    rw [binaryComplexReflection_im]
    exact point.im_pos⟩
  have point_eq : UpperHalfPlane.ofComplex (binaryComplexReflection point) = reflected :=
    UpperHalfPlane.ofComplex_apply reflected
  have first := classicalBinaryPrimitive_modular form degree weight_eq twist matrix point
  have second := classicalBinaryPrimitive_modular form degree weight_eq twist (modularReflection matrix) reflected
  have base_reflection := modularReflection_upper matrix UpperHalfPlane.I
  have base : UpperHalfPlane.ofComplex (binaryComplexReflection (UpperHalfPlane.I : ℂ)) = UpperHalfPlane.I := by
    change UpperHalfPlane.ofComplex (binaryComplexReflection Complex.I) = UpperHalfPlane.I
    rw [binaryComplexReflection_basepoint]
    exact UpperHalfPlane.ofComplex_apply UpperHalfPlane.I
  rw [base] at base_reflection
  have point_reflection := modularReflection_upper matrix point
  rw [point_eq] at point_reflection
  rw [← point_reflection, ← base_reflection] at second
  have reflected_relation := congrArg (binaryParityReflection degree) second
  rw [map_sub] at reflected_relation
  have intertwines := binaryParityReflection_modular_intertwines degree twist matrix
    (classicalBinaryPrimitive form degree reflected)
  change binaryParityReflection degree
    ((arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL (modularReflection matrix))
      (classicalBinaryPrimitive form degree reflected)) =
    action (binaryParityReflection degree (classicalBinaryPrimitive form degree (binaryComplexReflection point))) at intertwines
  rw [intertwines] at reflected_relation
  let a := classicalBinaryPrimitive form degree ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ)
  let b := binaryParityReflection degree (classicalBinaryPrimitive form degree
    (binaryComplexReflection ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ)))
  let c := classicalBinaryPrimitive form degree ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ)
  let d := binaryParityReflection degree (classicalBinaryPrimitive form degree
    (binaryComplexReflection ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))
  let e := classicalBinaryPrimitive form degree point
  let f := binaryParityReflection degree (classicalBinaryPrimitive form degree (binaryComplexReflection point))
  have first' : a - c = action e := first
  have second' : b - d = action f := reflected_relation
  change @Eq (Binary.HomogeneousPoly degree)
    ((2 : ℂ)⁻¹ • (a + (-1 : ℂ) ^ parity • b) - (2 : ℂ)⁻¹ • (c + (-1 : ℂ) ^ parity • d))
    (action ((2 : ℂ)⁻¹ • (e + (-1 : ℂ) ^ parity • f)))
  calc
    _ = (2 : ℂ)⁻¹ • ((a - c) + (-1 : ℂ) ^ parity • (b - d)) := by module
    _ = _ := by rw [first', second', map_smul, map_add, map_smul]

theorem classicalParityPrimitive_equivariant_iff_H1_zero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) (parity : ℕ) :
    (∃ potential : Binary.HomogeneousPoly degree,
      ∀ (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane),
        classicalParityPrimitive form degree parity ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ) +
          potential = (modularBinaryRep degree twist).ρ matrix
            (classicalParityPrimitive form degree parity point + potential)) ↔
      groupCohomology.H1π (modularBinaryRep degree twist)
        (modularCocycleParity degree twist parity (classicalBinaryCocycle form degree weight_eq twist)) = 0 := by
  constructor
  · rintro ⟨potential, equivariant⟩
    apply (groupCohomology.H1π_eq_zero_iff _).mpr
    refine ⟨potential, funext fun matrix => ?_⟩
    let action : Module.End ℂ (Binary.HomogeneousPoly degree) := (modularBinaryRep degree twist).ρ matrix
    have value := equivariant matrix UpperHalfPlane.I
    change classicalParityPrimitive form degree parity
      ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) + potential =
        action (classicalParityPrimitive form degree parity Complex.I + potential) at value
    rw [classicalParityPrimitive_basepoint, zero_add] at value
    exact (sub_eq_iff_eq_add.mpr value.symm).trans
      (classicalParityPrimitive_cocycle form degree weight_eq twist parity matrix)
  · intro zero
    obtain ⟨potential, boundary⟩ := (groupCohomology.H1π_eq_zero_iff _).mp zero
    refine ⟨potential, ?_⟩
    intro matrix point
    let action : Module.End ℂ (Binary.HomogeneousPoly degree) := (modularBinaryRep degree twist).ρ matrix
    let moved := classicalParityPrimitive form degree parity
      ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ)
    let anchor := classicalParityPrimitive form degree parity
      ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ)
    let initial := classicalParityPrimitive form degree parity point
    let q : Binary.HomogeneousPoly degree := potential
    have period : anchor = action q - q :=
      (classicalParityPrimitive_cocycle form degree weight_eq twist parity matrix).trans
        (congrFun boundary matrix).symm
    have relation : moved - anchor = action initial :=
      classicalParityPrimitive_modular form degree weight_eq twist parity matrix point
    change @Eq (Binary.HomogeneousPoly degree) (moved + q) (action (initial + q))
    calc
      moved + q = (moved - anchor) + (anchor + q) := by abel
      _ = action initial + action q := by rw [relation, period]; abel
      _ = action (initial + q) := (map_add action initial q).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
