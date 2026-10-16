module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.UpperHalfFactorization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cusp_realize_circle_pow (cusp : CuspidalRepresentation) (weight : ℕ)
    (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (angle : Circle) (argument : BinaryAdelicGL) :
    cusp.realize vector (argument * atInfinity (binaryCircleRotation angle)) =
      (angle : ℂ) ^ weight * cusp.realize vector argument := by
  obtain ⟨parameter, rfl⟩ := Circle.exp_surjective angle
  have character := cusp_realize_rotation_character cusp weight vector rotation parameter argument
  have exponent : Complex.I * (weight : ℂ) * (parameter : ℂ) =
      (weight : ℂ) * ((parameter : ℂ) * Complex.I) := by ring
  simpa only [binaryRotationPath, exponent, Complex.exp_nat_mul, Circle.coe_exp] using character

theorem cohomological_realize_complexUnit {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℕ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (value : ℂ) (nonzero : value ≠ 0) (argument : BinaryAdelicGL) :
    cusp.realize vector (argument * atInfinity (binaryComplexUnit value nonzero)) =
      (value / (‖value‖ : ℂ)) ^ weight * cusp.realize vector argument := by
  rw [binaryComplexUnit_polar, binary_atInfinity_mul, ← mul_assoc,
    cusp_realize_circle_pow cusp weight vector rotation]
  rw [cohomological_realize_positive_scalar cohomological _ (norm_pos_iff.mpr nonzero)]
  rfl

theorem cohomological_upperHalfOrbit_action {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℕ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (argument : BinaryAdelicGL) (matrix : BinaryRealGL)
    (positive : 0 < (GeneralLinearGroup.det matrix : ℝ)) (point : UpperHalfPlane) :
    cuspUpperHalfOrbit cusp vector (argument * atInfinity matrix) point =
      (starRingEnd ℂ (UpperHalfPlane.denom matrix point) /
        (‖UpperHalfPlane.denom matrix point‖ : ℂ)) ^ weight *
          cuspUpperHalfOrbit cusp vector argument (matrix • point : UpperHalfPlane) := by
  simp only [cuspUpperHalfOrbit_apply]
  rw [mul_assoc, ← binary_atInfinity_mul, binaryUpperHalfPoint_factor matrix positive point,
    binary_atInfinity_mul, ← mul_assoc, cohomological_realize_complexUnit cohomological weight vector rotation,
    Complex.norm_conj]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
