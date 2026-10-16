module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityBoundary

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem classicalBinaryPrimitive_unique {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (primitive : ℂ → Binary.HomogeneousPoly degree)
    (basepoint : primitive Complex.I = 0)
    (derivative : ∀ (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) (point : ℂ), 0 < point.im →
      HasDerivAt (fun point => functional (primitive point))
        (functional (classicalBinaryForm form degree point)) point)
    (point : ℂ) (positive : 0 < point.im) :
    primitive point = classicalBinaryPrimitive form degree point := by
  apply (binaryStandardBasis degree).ext_elem
  intro position
  let functional := (binaryStandardBasis degree).coord position
  let difference : ℂ → ℂ := fun point =>
    functional (primitive point) - functional (classicalBinaryPrimitive form degree point)
  have zero_derivative (argument : ℂ) (positive : 0 < argument.im) : HasDerivAt difference 0 argument := by
    have result := (derivative functional argument positive).sub
      (classicalBinaryPrimitive_hasDerivAt form degree functional argument positive)
    rw [sub_self] at result
    convert result using 1
  have constant : difference point = difference Complex.I := by
    apply (convex_halfSpace_im_gt 0).is_const_of_fderivWithin_eq_zero
      (fun point positive => (zero_derivative point positive).differentiableAt.differentiableWithinAt)
      (fun point positive => ?_) positive (by simp)
    rw [fderivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet positive]
    simpa using (zero_derivative point positive).hasFDerivAt.fderiv
  have zero : difference Complex.I = 0 := by
    simp [difference, basepoint, classicalBinaryPrimitive_basepoint]
  exact sub_eq_zero.mp (constant.trans zero)

theorem classicalBinaryForm_add {weight : ℤ}
    (first second : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (point : ℂ) :
    classicalBinaryForm (first + second) degree point =
      classicalBinaryForm first degree point + classicalBinaryForm second degree point := by
  simp [classicalBinaryForm, add_smul]

theorem classicalBinaryForm_smul {weight : ℤ} (scalar : ℂ)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (point : ℂ) :
    classicalBinaryForm (scalar • form) degree point = scalar • classicalBinaryForm form degree point := by
  simp [classicalBinaryForm, smul_smul]

theorem classicalBinaryPrimitive_add {weight : ℤ}
    (first second : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (point : ℂ) (positive : 0 < point.im) :
    classicalBinaryPrimitive (first + second) degree point =
      classicalBinaryPrimitive first degree point + classicalBinaryPrimitive second degree point := by
  symm
  apply classicalBinaryPrimitive_unique (first + second) degree
    (fun point => classicalBinaryPrimitive first degree point + classicalBinaryPrimitive second degree point)
    (by rw [classicalBinaryPrimitive_basepoint, classicalBinaryPrimitive_basepoint, add_zero]) _ point positive
  intro functional argument argument_positive
  simp only [map_add, classicalBinaryForm_add]
  exact (classicalBinaryPrimitive_hasDerivAt first degree functional argument argument_positive).add
    (classicalBinaryPrimitive_hasDerivAt second degree functional argument argument_positive)

theorem classicalBinaryPrimitive_smul {weight : ℤ} (scalar : ℂ)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (point : ℂ) (positive : 0 < point.im) :
    classicalBinaryPrimitive (scalar • form) degree point = scalar • classicalBinaryPrimitive form degree point := by
  symm
  apply classicalBinaryPrimitive_unique (scalar • form) degree
    (fun point => scalar • classicalBinaryPrimitive form degree point)
    (by rw [classicalBinaryPrimitive_basepoint, smul_zero]) _ point positive
  intro functional argument argument_positive
  simp only [map_smul, classicalBinaryForm_smul, smul_eq_mul]
  exact (classicalBinaryPrimitive_hasDerivAt form degree functional argument argument_positive).const_mul scalar

def classicalBinaryCocycleMap (weight : ℤ) (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight →ₗ[ℂ]
      groupCohomology.cocycles₁ (modularBinaryRep degree twist) where
  toFun form := classicalBinaryCocycle form degree weight_eq twist
  map_add' first second := by
    apply groupCohomology.cocycles₁_ext
    intro matrix
    exact classicalBinaryPrimitive_add first second degree _
      (SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I).im_pos
  map_smul' scalar form := by
    apply groupCohomology.cocycles₁_ext
    intro matrix
    exact classicalBinaryPrimitive_smul scalar form degree _
      (SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I).im_pos

def arithmeticParityCocycleMap (degree : ℕ) (twist : ℤ) (even : Even degree)
    (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    groupCohomology.cocycles₁ (modularBinaryRep degree twist) →ₗ[ℂ]
      groupCohomology.cocycles₁ (arithmeticBinaryRep degree twist) where
  toFun := arithmeticParityCocycle degree twist even parity sign
  map_add' := arithmeticParityCocycle_add degree twist even parity sign
  map_smul' scalar cycle := by
    apply groupCohomology.cocycles₁_ext
    intro matrix
    change modularCocycleParity degree twist parity (scalar • cycle)
      (splitRadicalCoordinate integralDeterminantSplitting matrix) = _
    rw [map_smul]
    rfl

def classicalArithmeticCocycleMap (weight : ℤ) (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2)
    (even : Even degree) (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight →ₗ[ℂ]
      groupCohomology.cocycles₁ (arithmeticBinaryRep degree twist) :=
  (arithmeticParityCocycleMap degree twist even parity sign).comp
    (classicalBinaryCocycleMap weight degree weight_eq twist)

theorem classicalArithmeticCocycleMap_apply (weight : ℤ) (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2)
    (even : Even degree) (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight) :
    classicalArithmeticCocycleMap weight degree weight_eq even twist parity sign form =
      classicalArithmeticCocycle form degree weight_eq even twist parity sign := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
