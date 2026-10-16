module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationSmooth

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem circle_normalized_toCircle (parameter : ℝ) :
    AddCircle.toCircle (((parameter / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) = Circle.exp parameter := by
  rw [AddCircle.toCircle_apply_mk]
  congr 1
  field_simp

theorem circle_fourier_normalized (weight : ℤ) (parameter : ℝ) :
    fourier weight ((parameter / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) =
      Complex.exp (Complex.I * (weight : ℂ) * (parameter : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem cuspRotationProjection_real_rotation (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H) (parameter : ℝ) :
    cusp.π (atInfinity (binaryRotationPath parameter)) (cuspRotationProjection cusp weight vector) =
      Complex.exp (Complex.I * (weight : ℂ) * (parameter : ℂ)) • cuspRotationProjection cusp weight vector := by
  have character := cuspRotationProjection_rotation cusp weight vector
    ((parameter / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))
  simpa only [cuspCircularOrbit, circle_normalized_toCircle, circle_fourier_normalized, binaryRotationPath] using character

theorem rotation_character_hasDerivAt_zero {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (weight : ℤ) (vector : H) :
    HasDerivAt (fun parameter : ℝ => Complex.exp (Complex.I * (weight : ℂ) * (parameter : ℂ)) • vector)
      ((Complex.I * (weight : ℂ)) • vector) 0 := by
  have derivative := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (Complex.I * (weight : ℂ))).cexp
  simpa only [id_eq, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_one, mul_one, one_mul] using
    derivative.smul_const vector

theorem cuspSmoothRotationProjection_eigenvector (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) :
    cuspRotationOperator cusp (cuspSmoothRotationProjection cusp weight vector) =
      (Complex.I * (weight : ℂ)) • cuspSmoothRotationProjection cusp weight vector := by
  let projected := cuspSmoothRotationProjection cusp weight vector
  have actual := cuspSmoothAction_path_hasDerivAt cusp projected binaryRotationPath binaryRotationDirection 0
    binaryRotationPath_zero binaryRotationPath_entry_hasDerivAt_zero
  have scalar := rotation_character_hasDerivAt_zero weight projected.val
  have equal : (fun parameter : ℝ => (cuspSmoothAction cusp (atInfinity (binaryRotationPath parameter)) projected).val) =
      (fun parameter : ℝ => Complex.exp (Complex.I * (weight : ℂ) * (parameter : ℂ)) • projected.val) := by
    funext parameter
    exact cuspRotationProjection_real_rotation cusp weight vector.val parameter
  rw [equal] at actual
  apply Subtype.ext
  exact actual.unique scalar

theorem cuspSmoothRotationProjection_exists_nonzero (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) : ∃ weight : ℤ, cuspSmoothRotationProjection cusp weight vector ≠ 0 := by
  have hilbert_nonzero : vector.val ≠ 0 := by
    intro zero
    exact nonzero (Subtype.ext zero)
  obtain ⟨weight, projected_nonzero⟩ := cuspRotationProjection_exists_nonzero cusp vector.val hilbert_nonzero
  refine ⟨weight, fun zero => projected_nonzero ?_⟩
  exact congrArg Subtype.val zero

theorem cohomological_smooth_projection_gap {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℤ) (vector : cusp.smooth)
    (nonzero : cuspSmoothRotationProjection cusp weight vector ≠ 0) :
    (degree : ℝ) + 3 ≤ |(weight : ℝ)| := by
  apply cohomological_rotation_weight_gap cohomological weight
    (cuspSmoothRotationProjection cusp weight vector) nonzero
  simpa only [Complex.ofReal_intCast] using cuspSmoothRotationProjection_eigenvector cusp weight vector

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
