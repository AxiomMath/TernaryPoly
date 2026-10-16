module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FullLadders
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryAffineGenerator (direction : ℂ) : BinaryRealMatrix :=
  !![direction.im / 2, direction.re; 0, -direction.im / 2]

theorem binaryAffineGenerator_horizontal : binaryAffineGenerator 1 = binaryHorizontalGenerator := by
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [binaryAffineGenerator, binaryHorizontalGenerator]

theorem binaryAffineGenerator_vertical : binaryAffineGenerator Complex.I = binaryDiagonalGenerator := by
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [binaryAffineGenerator, binaryDiagonalGenerator]

theorem binaryUpperSectionMatrix_hasDerivAt (direction : ℂ) :
    HasDerivAt (fun parameter : ℝ => binaryUpperSectionMatrix (Complex.I + parameter • direction))
      (binaryAffineGenerator direction) 0 := by
  have real_derivative : HasDerivAt (fun parameter : ℝ => (Complex.I + parameter • direction).re) direction.re 0 := by
    convert (hasDerivAt_id (0 : ℝ)).mul_const direction.re using 1 <;> first | simp [Complex.real_smul]
  have imaginary_derivative : HasDerivAt (fun parameter : ℝ => (Complex.I + parameter • direction).im) direction.im 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const direction.im).const_add 1 using 1 <;> first | simp [Complex.real_smul]
  have root_derivative : HasDerivAt (fun parameter : ℝ => Real.sqrt (Complex.I + parameter • direction).im)
      (direction.im / 2) 0 := by
    simpa only [zero_smul, add_zero, Complex.I_im, Real.sqrt_one, mul_one] using imaginary_derivative.sqrt (by simp)
  have root_nonzero : Real.sqrt (Complex.I + (0 : ℝ) • direction).im ≠ 0 := by simp
  apply hasDerivAt_pi.mpr
  intro row
  apply hasDerivAt_pi.mpr
  intro column
  fin_cases row <;> fin_cases column
  · simpa [binaryUpperSectionMatrix, binaryAffineGenerator] using root_derivative
  · convert real_derivative.div root_derivative root_nonzero using 1 <;> first | rfl | simp [binaryAffineGenerator]
  · simpa [binaryUpperSectionMatrix, binaryAffineGenerator] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · convert root_derivative.inv root_nonzero using 1 <;> first | simp [binaryUpperSectionMatrix, binaryAffineGenerator, one_div, neg_div, Pi.inv_def]

theorem cuspMatrixDifferential_affine (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) 1) (direction : ℂ) :
    cuspMatrixDifferential cusp vector (binaryAffineGenerator direction) =
      fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction := by
  have affine_regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I := by
    have section_regular := (binaryUpperSectionMatrix_contDiffOn (order := 1)).differentiableOn (by norm_num)
    have regular_at_section : DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) (binaryUpperSectionMatrix Complex.I) :=
      binaryUpperSectionMatrix_I.symm ▸ regular
    have derivative := regular_at_section.comp Complex.I
      (section_regular.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simp)))
    exact derivative
  have line_derivative : HasDerivAt (fun parameter : ℝ => Complex.I + parameter • direction) direction 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add Complex.I using 1 <;> first | rfl | simp
  have first := regular.hasFDerivAt.comp_hasDerivAt_of_eq 0 (binaryUpperSectionMatrix_hasDerivAt direction)
    (by simp [binaryUpperSectionMatrix_I])
  have second := affine_regular.hasFDerivAt.comp_hasDerivAt_of_eq 0 line_derivative (by simp)
  exact first.unique second

theorem binaryRotationMatrix_exp_hasDerivAt :
    HasDerivAt (fun parameter : ℝ => binaryRotationMatrix (Circle.exp parameter)) binaryRotationGenerator 0 := by
  apply hasDerivAt_pi.mpr
  intro row
  apply hasDerivAt_pi.mpr
  intro column
  fin_cases row <;> fin_cases column
  all_goals simp only [binaryRotationMatrix, binaryRotations, MonoidHom.coe_mk, OneHom.coe_mk,
    binaryRotation, binaryRotationGenerator, Circle.coe_exp, Complex.exp_ofReal_mul_I]
  · convert Real.hasDerivAt_cos 0 using 1 <;> first | simp
    funext parameter
    exact Complex.cos_ofReal_re parameter
  · convert (Real.hasDerivAt_sin 0).neg using 1 <;> first | simp
    funext parameter
    exact congrArg Neg.neg (Complex.sin_ofReal_re parameter)
  · convert Real.hasDerivAt_sin 0 using 1 <;> first | simp
    funext parameter
    exact Complex.sin_ofReal_re parameter
  · convert Real.hasDerivAt_cos 0 using 1 <;> first | simp
    funext parameter
    exact Complex.cos_ofReal_re parameter

theorem cuspMatrixDifferential_rotation_curve (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) 1) :
    HasDerivAt (fun parameter : ℝ => cusp.π (atInfinity (binaryRotations (Circle.exp parameter))) vector)
      (cuspMatrixDifferential cusp vector binaryRotationGenerator) 0 := by
  have derivative := regular.hasFDerivAt.comp_hasDerivAt_of_eq 0 binaryRotationMatrix_exp_hasDerivAt
    (by simp [binaryRotationMatrix])
  have equality : (fun parameter : ℝ => cuspMatrixOrbit cusp vector (binaryRotationMatrix (Circle.exp parameter))) =
      (fun parameter : ℝ => cusp.π (atInfinity (binaryRotations (Circle.exp parameter))) vector) := by
    funext parameter
    rw [cuspMatrixOrbit, binaryRotationMatrix, invertibleMatrix_coe]
  change HasDerivAt (fun parameter => cuspMatrixOrbit cusp vector (binaryRotationMatrix (Circle.exp parameter))) _ 0 at derivative
  rw [equality] at derivative
  convert derivative using 1
  rfl

theorem circleExp_zpow_hasDerivAt (weight : ℤ) :
    HasDerivAt (fun parameter : ℝ => (Circle.exp parameter : ℂ) ^ weight) (Complex.I * (weight : ℂ)) 0 := by
  have exponential : HasDerivAt (fun parameter : ℝ => (Circle.exp parameter : ℂ)) Complex.I 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp using 1 <;>
      first | rfl | simp
  have derivative := hasDerivAt_complex_zpow_comp (fun parameter : ℝ => (Circle.exp parameter : ℂ)) 1 Complex.I weight
    (by simp) one_ne_zero exponential
  simpa only [one_zpow, mul_one, mul_comm] using derivative

theorem cuspRotationWeight_hasDerivAt (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector) :
    HasDerivAt (fun parameter : ℝ => cusp.π (atInfinity (binaryRotations (Circle.exp parameter))) vector)
      ((Complex.I * (weight : ℂ)) • vector) 0 := by
  simpa only [rotation] using (circleExp_zpow_hasDerivAt weight).smul_const vector

theorem cuspMatrixDifferential_rotation_weight (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) 1)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector) :
    cuspMatrixDifferential cusp vector binaryRotationGenerator = (Complex.I * (weight : ℂ)) • vector :=
  (cuspMatrixDifferential_rotation_curve cusp vector regular).unique (cuspRotationWeight_hasDerivAt cusp weight vector rotation)

theorem cuspFullRaisingVector_affine (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) 1) :
    cuspFullRaisingVector cusp vector =
      fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 +
        Complex.I • fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I +
          (1/2 : ℝ) • cuspMatrixDifferential cusp vector binaryRotationGenerator := by
  rw [cuspFullRaisingVector, binarySymmetricGenerator_decomposition, map_add, map_smul,
    ← binaryAffineGenerator_horizontal, ← binaryAffineGenerator_vertical,
    cuspMatrixDifferential_affine cusp vector regular, cuspMatrixDifferential_affine cusp vector regular]
  abel

theorem cuspFullRaisingVector_eq_weighted (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspMatrixOrbit cusp vector) 1)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector) :
    cuspFullRaisingVector cusp vector = cuspRaisingVector cusp weight vector := by
  rw [cuspFullRaisingVector_affine cusp vector regular, cuspMatrixDifferential_rotation_weight cusp weight vector regular rotation]
  simp only [cuspRaisingVector, RCLike.real_smul_eq_coe_smul (K := ℂ), map_div₀, map_one, map_ofNat]
  module

theorem cuspMatrixDifferential_rotation_inner (cusp : CuspidalRepresentation) (weight : ℤ) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspMatrixOrbit cusp test) 1)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector) :
    inner ℂ (cuspMatrixDifferential cusp test binaryRotationGenerator) vector =
      -(Complex.I * (weight : ℂ)) * inner ℂ test vector := by
  have skew := cuspUnitary_derivative_skew cusp
    (fun parameter => atInfinity (binaryRotations (Circle.exp parameter))) (by simp [atInfinity_one])
    test vector _ _ (cuspMatrixDifferential_rotation_curve cusp test regular)
    (cuspRotationWeight_hasDerivAt cusp weight vector rotation)
  rw [inner_smul_right] at skew
  linear_combination skew

theorem cuspFullRaisingVector_inner_weight (cusp : CuspidalRepresentation) (weight : ℤ) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspMatrixOrbit cusp test) 1)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector) :
    inner ℂ (cuspFullRaisingVector cusp test) vector = inner ℂ (cuspRaisingVector cusp weight test) vector := by
  rw [cuspFullRaisingVector_affine cusp test regular]
  simp only [cuspRaisingVector, inner_add_left, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
    map_div₀, map_one, map_ofNat, Complex.conj_I, map_mul, map_intCast,
    cuspMatrixDifferential_rotation_inner cusp weight test vector regular rotation]
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
