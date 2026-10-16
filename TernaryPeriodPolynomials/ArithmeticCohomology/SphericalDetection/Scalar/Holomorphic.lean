module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AntiholomorphicCircleDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspScalarDiskOrbit_differentiableAt_zero (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    DifferentiableAt ℂ (cuspScalarDiskOrbit cusp halfWeight vector base) 0 := by
  apply differentiableAt_complex_of_antiholomorphic_circleMean_zero
  · exact (cuspScalarDiskOrbit_analytic cusp halfWeight vector base).contDiffOn
      Metric.isOpen_ball.uniqueDiffOn
  · exact cuspScalarDisk_antiholomorphic_mean_zero cusp halfWeight vector spherical rotation holomorphic base

theorem binaryDiskCoordinate_I : binaryDiskCoordinate Complex.I = 0 := by
  simp [binaryDiskCoordinate]

theorem binaryDiskCoordinate_differentiableAt_I : DifferentiableAt ℂ binaryDiskCoordinate Complex.I := by
  apply (differentiableAt_id.sub_const Complex.I).div (differentiableAt_id.add_const Complex.I)
  have nonzero : Complex.I + Complex.I ≠ 0 := by
    intro equality
    have imaginary := congrArg Complex.im equality
    norm_num at imaginary
  exact nonzero

theorem binaryDiskCoordinate_sub_ne_zero (point : ℂ) (denominator : point + Complex.I ≠ 0) :
    1 - binaryDiskCoordinate point ≠ 0 := by
  have formula : 1 - binaryDiskCoordinate point = (2 * Complex.I) / (point + Complex.I) := by
    unfold binaryDiskCoordinate
    field_simp
    ring
  rw [formula]
  exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) denominator

theorem binaryDiskPoint_coordinate (point : ℂ) (denominator : point + Complex.I ≠ 0) :
    binaryDiskPoint (binaryDiskCoordinate point) = point := by
  have other := binaryDiskCoordinate_sub_ne_zero point denominator
  unfold binaryDiskPoint binaryDiskCoordinate at *
  field_simp
  ring

theorem cuspScalarWeightedRealization_differentiableAt_I (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    DifferentiableAt ℂ (cuspScalarWeightedRealization cusp halfWeight vector base) Complex.I := by
  have disk_regular := cuspScalarDiskOrbit_differentiableAt_zero cusp halfWeight vector spherical rotation holomorphic base
  have at_coordinate : DifferentiableAt ℂ (cuspScalarDiskOrbit cusp halfWeight vector base)
      (binaryDiskCoordinate Complex.I) := by rwa [binaryDiskCoordinate_I]
  have composed := at_coordinate.comp Complex.I binaryDiskCoordinate_differentiableAt_I
  have factor : DifferentiableAt ℂ (fun point => (1 - binaryDiskCoordinate point) ^ (-(2 * halfWeight))) Complex.I :=
    ((differentiableAt_const 1).sub binaryDiskCoordinate_differentiableAt_I).zpow
      (Or.inl (by simp [binaryDiskCoordinate_I]))
  apply (factor.mul composed).congr_of_eventuallyEq
  have nearby : ∀ᶠ point : ℂ in nhds Complex.I, point + Complex.I ≠ 0 := by
    apply (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const).mem_nhds
    intro equality
    have imaginary := congrArg Complex.im equality
    norm_num at imaginary
  filter_upwards [nearby] with point denominator
  change cuspScalarWeightedRealization cusp halfWeight vector base point =
    (1 - binaryDiskCoordinate point) ^ (-(2 * halfWeight)) *
      cuspScalarDiskOrbit cusp halfWeight vector base (binaryDiskCoordinate point)
  rw [cuspScalarDiskOrbit, binaryDiskPoint_coordinate point denominator, ← mul_assoc,
    ← zpow_add₀ (binaryDiskCoordinate_sub_ne_zero point denominator), neg_add_cancel, zpow_zero, one_mul]

theorem cuspScalarAffineRealization_affine (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryAdelicGL) (point argument : UpperHalfPlane) :
    cuspScalarAffineRealization cusp vector base ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
      cuspScalarAffineRealization cusp vector (base * atInfinity (binarySymmetricSection point)) argument := by
  have matrix_equality := binaryUpperSectionMatrix_affine_mul (point : ℂ) (argument : ℂ)
    point.im_pos argument.im_pos
  change binaryUpperSectionMatrix ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
    binaryUpperSectionMatrix point * binaryUpperSectionMatrix argument at matrix_equality
  rw [cuspScalarAffineRealization, matrix_equality,
    invertibleMatrix_mul _ _ (binaryUpperSectionMatrix_invertible point point.im_pos)
      (binaryUpperSectionMatrix_invertible argument argument.im_pos), atInfinity_mul,
    binaryUpperSectionMatrix_coe point, invertibleMatrix_coe, ← mul_assoc]
  rfl

theorem cuspScalarWeightedRealization_affine (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) (point argument : UpperHalfPlane) :
    cuspScalarWeightedRealization cusp halfWeight vector base
      ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
      point.im ^ halfWeight • cuspScalarWeightedRealization cusp halfWeight vector
        (base * atInfinity (binarySymmetricSection point)) argument := by
  simp only [cuspScalarWeightedRealization, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_mul, zero_add, add_zero, UpperHalfPlane.coe_im, mul_zpow,
    cuspScalarAffineRealization_affine, smul_smul]

/-- Holomorphicity of the actual scalar realization follows from smooth rotation differences. -/
theorem cuspScalarWeightedRealization_holomorphic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector base)
      UpperHalfPlane.upperHalfPlaneSet := by
  intro point positive
  let upper : UpperHalfPlane := ⟨point, positive⟩
  let pullback : ℂ → ℂ := fun argument => (upper.im : ℂ)⁻¹ * (argument - (upper.re : ℂ))
  have pullback_im (argument : ℂ) : (pullback argument).im = upper.im⁻¹ * argument.im := by
    simp [pullback, ← Complex.ofReal_inv]
  have pullback_basepoint : pullback point = Complex.I := by
    apply Complex.ext
    · simp [pullback, ← Complex.ofReal_inv, upper]
    · rw [pullback_im]
      exact inv_mul_cancel₀ (ne_of_gt positive)
  have recovers (argument : ℂ) : (upper.re : ℂ) + (upper.im : ℂ) * pullback argument = argument := by
    dsimp only [pullback]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt upper.im_pos), one_mul, add_sub_cancel]
  have at_base := cuspScalarWeightedRealization_differentiableAt_I cusp halfWeight vector spherical rotation holomorphic
    (base * atInfinity (binarySymmetricSection upper))
  have pullback_regular : DifferentiableAt ℂ pullback point :=
    (differentiableAt_id.sub_const (upper.re : ℂ)).const_mul (upper.im : ℂ)⁻¹
  have transformed := ((pullback_basepoint.symm ▸ at_base).comp point pullback_regular).const_smul
    (upper.im ^ halfWeight)
  apply DifferentiableAt.differentiableWithinAt
  apply transformed.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive] with argument argument_positive
  have pulled_positive : 0 < (pullback argument).im := by
    rw [pullback_im]
    exact mul_pos (inv_pos.mpr upper.im_pos) argument_positive
  have formula := cuspScalarWeightedRealization_affine cusp halfWeight vector base upper
    ⟨pullback argument, pulled_positive⟩
  rw [recovers] at formula
  exact formula

end TernaryPeriodPolynomials.SphericalDetection.Helpers
