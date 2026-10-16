module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.BinaryForm
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem classicalBinaryForm_exists_primitive {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) :
    ∃ primitive : ℂ → Binary.HomogeneousPoly degree, primitive Complex.I = 0 ∧
      ∀ (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) (point : ℂ), 0 < point.im →
        HasDerivAt (fun point => functional (primitive point))
          (functional (classicalBinaryForm form degree point)) point := by
  have exists_coordinate (position : Fin (degree + 1)) :=
    (convex_halfSpace_im_gt 0).exists_forall_hasDerivWithinAt
      (classicalBinaryForm_coord_holomorphic form degree ((binaryStandardBasis degree).coord position))
  choose coordinate derivative using exists_coordinate
  let primitive : ℂ → Binary.HomogeneousPoly degree := fun point =>
    ∑ position : Fin (degree + 1), (coordinate position point - coordinate position Complex.I) •
      binaryStandardBasis degree position
  refine ⟨primitive, ?_, ?_⟩
  · simp [primitive]
  · intro functional point positive
    have values : (fun point => functional (primitive point)) =
        fun point => ∑ position : Fin (degree + 1),
          (coordinate position point - coordinate position Complex.I) *
            functional (binaryStandardBasis degree position) := by
      funext point
      simp only [primitive, map_sum, map_smul, smul_eq_mul]
    have differential : functional (classicalBinaryForm form degree point) =
        ∑ position : Fin (degree + 1),
          (binaryStandardBasis degree).coord position (classicalBinaryForm form degree point) *
            functional (binaryStandardBasis degree position) := by
      conv_lhs => rw [← (binaryStandardBasis degree).sum_repr (classicalBinaryForm form degree point)]
      simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
    rw [values, differential]
    apply HasDerivAt.fun_sum
    intro position _
    exact (((derivative position point positive).hasDerivAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive)).sub_const
        (coordinate position Complex.I)).mul_const (functional (binaryStandardBasis degree position))

def classicalBinaryPrimitive {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) : ℂ → Binary.HomogeneousPoly degree :=
  (classicalBinaryForm_exists_primitive form degree).choose

theorem classicalBinaryPrimitive_basepoint {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) : classicalBinaryPrimitive form degree Complex.I = 0 :=
  (classicalBinaryForm_exists_primitive form degree).choose_spec.1

theorem classicalBinaryPrimitive_hasDerivAt {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (point : ℂ) (positive : 0 < point.im) :
    HasDerivAt (fun point => functional (classicalBinaryPrimitive form degree point))
      (functional (classicalBinaryForm form degree point)) point :=
  (classicalBinaryForm_exists_primitive form degree).choose_spec.2 functional point positive

theorem classicalBinaryPrimitive_modular {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane) :
    classicalBinaryPrimitive form degree ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ) -
        classicalBinaryPrimitive form degree
          ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL matrix)
        (classicalBinaryPrimitive form degree point) := by
  let action : Binary.HomogeneousPoly degree →ₗ[ℂ] Binary.HomogeneousPoly degree :=
    (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL matrix)
  let transform : ℂ → ℂ := fun point =>
    ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.ofComplex point : UpperHalfPlane) : ℂ)
  let difference : ℂ → Binary.HomogeneousPoly degree := fun point =>
    classicalBinaryPrimitive form degree (transform point) - action (classicalBinaryPrimitive form degree point)
  have determinant : ((SpecialLinearGroup.mapGL ℝ matrix).val).det = 1 := by
    change ((GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ matrix) : ℝˣ) : ℝ) = 1
    simp
  have zero_derivative (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
      (point : ℂ) (positive : 0 < point.im) :
      HasDerivAt (fun point => functional (difference point)) 0 point := by
    let upper : UpperHalfPlane := ⟨point, positive⟩
    let moved : UpperHalfPlane := SpecialLinearGroup.mapGL ℝ matrix • upper
    have transform_derivative :=
      (UpperHalfPlane.hasStrictDerivAt_smul (show 0 < (SpecialLinearGroup.mapGL ℝ matrix).val.det by rw [determinant]; norm_num)
        upper).hasDerivAt
    rw [determinant, Complex.ofReal_one, one_div] at transform_derivative
    have upper_eq : UpperHalfPlane.ofComplex point = upper := UpperHalfPlane.ofComplex_apply upper
    have first_derivative := classicalBinaryPrimitive_hasDerivAt form degree functional moved moved.im_pos
    have moved_eq : (moved : ℂ) = transform point := by simp only [transform, upper_eq, moved]
    rw [moved_eq] at first_derivative
    have first := first_derivative.comp point transform_derivative
    have second := classicalBinaryPrimitive_hasDerivAt form degree (functional.comp action) point positive
    have transformed := congrArg functional (classicalBinaryForm_modular form degree weight_eq twist matrix upper)
    change functional ((UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ matrix) point ^ 2)⁻¹ •
      classicalBinaryForm form degree moved) = functional (action (classicalBinaryForm form degree point)) at transformed
    rw [map_smul, smul_eq_mul] at transformed
    have result := first.sub second
    have cancel : functional (classicalBinaryForm form degree moved) *
        (UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ matrix) point ^ 2)⁻¹ -
          (functional.comp action) (classicalBinaryForm form degree point) = 0 := by
      rw [mul_comm, transformed]
      simp only [LinearMap.comp_apply, sub_self]
    rw [← moved_eq, cancel] at result
    convert result using 1
    all_goals first | (solve | ext) | (funext argument; exact map_sub functional _ _)
  have constant (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) :
      functional (difference point) = functional (difference Complex.I) := by
    apply (convex_halfSpace_im_gt 0).is_const_of_fderivWithin_eq_zero
      (fun point positive => (zero_derivative functional point positive).differentiableAt.differentiableWithinAt)
      (fun point positive => ?_) point.im_pos (by simp)
    rw [fderivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet positive]
    simpa using (zero_derivative functional point positive).hasFDerivAt.fderiv
  have equal : difference point = difference Complex.I := by
    apply (binaryStandardBasis degree).ext_elem
    intro position
    exact constant ((binaryStandardBasis degree).coord position)
  have basepoint : difference Complex.I = classicalBinaryPrimitive form degree
      ((SpecialLinearGroup.mapGL ℝ matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
    have base : UpperHalfPlane.ofComplex Complex.I = UpperHalfPlane.I :=
      UpperHalfPlane.ofComplex_apply UpperHalfPlane.I
    simp [difference, transform, classicalBinaryPrimitive_basepoint, base]
  rw [basepoint] at equal
  change classicalBinaryPrimitive form degree (transform point) -
    action (classicalBinaryPrimitive form degree point) = _ at equal
  have moved : transform point = ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ) := by
    simp [transform]
  rw [moved] at equal
  exact sub_eq_of_eq_add (sub_eq_iff_eq_add'.mp equal)

theorem classicalBinaryPrimitive_imaginary_integral {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (lower upper : ℝ) (lower_positive : 0 < lower) (upper_positive : 0 < upper) :
    functional (classicalBinaryPrimitive form degree (Complex.I * (upper : ℂ))) -
        functional (classicalBinaryPrimitive form degree (Complex.I * (lower : ℂ))) =
      ∫ height : ℝ in lower..upper,
        functional (classicalBinaryForm form degree (Complex.I * (height : ℂ))) * Complex.I := by
  have positive (height : ℝ) (member : height ∈ Set.uIcc lower upper) : 0 < height :=
    lt_of_lt_of_le (lt_min lower_positive upper_positive) member.1
  have path : Continuous (fun height : ℝ => Complex.I * (height : ℂ)) := by fun_prop
  have image (height : ℝ) (member : height ∈ Set.uIcc lower upper) :
      Complex.I * (height : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa using positive height member
  have integrable : IntervalIntegrable
      (fun height : ℝ => functional (classicalBinaryForm form degree (Complex.I * (height : ℂ))) * Complex.I)
      MeasureTheory.volume lower upper :=
    (((classicalBinaryForm_coord_holomorphic form degree functional).continuousOn.comp
      path.continuousOn image).mul continuousOn_const).intervalIntegrable
  have derivative (height : ℝ) (member : height ∈ Set.uIcc lower upper) :
      HasDerivAt (fun height : ℝ => functional (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ))))
        (functional (classicalBinaryForm form degree (Complex.I * (height : ℂ))) * Complex.I) height := by
    have outer := (classicalBinaryPrimitive_hasDerivAt form degree functional
      (Complex.I * (height : ℂ)) (image height member)).hasFDerivAt.restrictScalars ℝ
    have inner : HasDerivAt (fun height : ℝ => Complex.I * (height : ℂ)) Complex.I height := by
      simpa using (Complex.ofRealCLM.hasDerivAt).const_mul Complex.I
    convert outer.comp_hasDerivAt height inner using 1
    all_goals first | rfl | simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt derivative integrable).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
