module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.InfinitesimalUnitarity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryUpperSectionMatrix_affine_mul (point argument : ℂ)
    (point_positive : 0 < point.im) (argument_positive : 0 < argument.im) :
    binaryUpperSectionMatrix ((point.re : ℂ) + (point.im : ℂ) * argument) =
      binaryUpperSectionMatrix point * binaryUpperSectionMatrix argument := by
  have point_root : Real.sqrt point.im ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr point_positive)
  have argument_root : Real.sqrt argument.im ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr argument_positive)
  have point_square := Real.sq_sqrt point_positive.le
  ext row column
  fin_cases row <;> fin_cases column
  all_goals norm_num [binaryUpperSectionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Real.sqrt_mul point_positive.le]
  all_goals field_simp
  all_goals linear_combination -argument.re * point_square

theorem cuspAffineOrbitVector_affine (cusp : CuspidalRepresentation) (vector : cusp.H)
    (point argument : UpperHalfPlane) :
    cuspAffineOrbitVector cusp vector ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
      cusp.π (atInfinity (binarySymmetricSection point)) (cuspAffineOrbitVector cusp vector argument) := by
  have matrix_equality := binaryUpperSectionMatrix_affine_mul (point : ℂ) (argument : ℂ)
    point.im_pos argument.im_pos
  change binaryUpperSectionMatrix ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
    binaryUpperSectionMatrix point * binaryUpperSectionMatrix argument at matrix_equality
  rw [cuspAffineOrbitVector, matrix_equality,
    invertibleMatrix_mul _ _ (binaryUpperSectionMatrix_invertible point point.im_pos)
      (binaryUpperSectionMatrix_invertible argument argument.im_pos), atInfinity_mul, map_mul,
    Module.End.mul_apply, binaryUpperSectionMatrix_coe point, invertibleMatrix_coe]
  rfl

theorem cuspAffineOrbitVector_derivative_translate (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : UpperHalfPlane) (direction : ℂ) :
    cuspAffineOrbitVector cusp (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction) point =
      point.im • fderiv ℝ (cuspAffineOrbitVector cusp vector) (point : ℂ) direction := by
  let orbit := cuspAffineOrbitVector cusp vector
  let affine : ℂ → ℂ := fun argument => (point.re : ℂ) + point.im • argument
  have affine_basepoint : affine Complex.I = (point : ℂ) := by
    apply Complex.ext <;> simp [affine, Complex.real_smul]
  have affine_derivative : HasFDerivAt affine (point.im • ContinuousLinearMap.id ℝ ℂ) Complex.I := by
    exact (hasFDerivAt_id Complex.I).const_smul point.im |>.const_add (point.re : ℂ)
  have at_point := (regular.differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds point.im_pos)).hasFDerivAt
  have at_basepoint := (regular.differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp))).hasFDerivAt
  have left_derivative := (affine_basepoint.symm ▸ at_point).comp Complex.I affine_derivative
  have right_derivative := ((cuspUnitaryOperator cusp (atInfinity (binarySymmetricSection point))).restrictScalars ℝ).hasFDerivAt.comp
    Complex.I at_basepoint
  have equality : orbit ∘ affine =ᶠ[nhds Complex.I]
      (fun argument => cusp.π (atInfinity (binarySymmetricSection point)) (orbit argument)) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      (show Complex.I.im > 0 by simp)] with argument member
    simpa only [orbit, affine, Function.comp_apply, Complex.real_smul] using
      cuspAffineOrbitVector_affine cusp vector point (⟨argument, member⟩ : UpperHalfPlane)
  have derivative_eq := left_derivative.unique (right_derivative.congr_of_eventuallyEq equality)
  have evaluated := congrArg (fun derivative : ℂ →L[ℝ] cusp.H => derivative direction) derivative_eq
  rw [affine_basepoint] at evaluated
  change fderiv ℝ orbit (point : ℂ) (point.im • direction) =
    cusp.π (atInfinity (binarySymmetricSection point)) (fderiv ℝ orbit Complex.I direction) at evaluated
  rw [map_smul] at evaluated
  rw [cuspAffineOrbitVector, binaryUpperSectionMatrix_coe point, invertibleMatrix_coe]
  exact evaluated.symm

theorem cuspAffineOrbitVector_derivative_contDiffOn (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (direction : ℂ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (cuspAffineOrbitVector cusp (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction))
      UpperHalfPlane.upperHalfPlaneSet := by
  have derivative_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fderiv ℝ (cuspAffineOrbitVector cusp vector)) UpperHalfPlane.upperHalfPlaneSet :=
    regular.fderiv_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet
      (WithTop.coe_le_coe.mpr (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤))
  have weighted := Complex.imCLM.contDiff.contDiffOn.smul
    (derivative_regular.clm_apply (contDiffOn_const (c := direction)))
  apply weighted.congr
  intro point member
  exact cuspAffineOrbitVector_derivative_translate cusp vector
    (regular.differentiableOn (by simp)) ⟨point, member⟩ direction

theorem cuspAffineOrbitVector_commutator (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet) :
    fderiv ℝ (cuspAffineOrbitVector cusp (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1)) Complex.I Complex.I -
      fderiv ℝ (cuspAffineOrbitVector cusp (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I)) Complex.I 1 =
        fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 := by
  have equality (direction : ℂ) :
      cuspAffineOrbitVector cusp (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction) =ᶠ[nhds Complex.I]
        fun point : ℂ => point.im • fderiv ℝ (cuspAffineOrbitVector cusp vector) point direction := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      (show Complex.I.im > 0 by simp)] with point member
    exact cuspAffineOrbitVector_derivative_translate cusp vector
      (regular.differentiableOn (by simp)) ⟨point, member⟩ direction
  rw [(equality 1).fderiv_eq, (equality Complex.I).fderiv_eq]
  apply weightedGradient_relation
  exact (regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I.im > 0 by simp))).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
