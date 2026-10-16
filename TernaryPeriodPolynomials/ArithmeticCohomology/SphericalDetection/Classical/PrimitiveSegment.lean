module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.BinaryPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointReconstruction

@[expose] public section


open GeneralEisenstein Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem classicalBinaryPrimitive_segment_integral {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (point : ℂ) (positive : 0 < point.im) :
    functional (classicalBinaryPrimitive form degree point) =
      ∫ parameter : ℝ in 0..1, (point - Complex.I) *
        functional (classicalBinaryForm form degree (Complex.I + parameter • (point - Complex.I))) := by
  let path : ℝ → ℂ := fun parameter => Complex.I + parameter • (point - Complex.I)
  have image (parameter : ℝ) (member : parameter ∈ Set.uIcc (0 : ℝ) 1) :
      path parameter ∈ UpperHalfPlane.upperHalfPlaneSet :=
    upperHalfPlane_straightPath ⟨point, positive⟩ (by simpa only [Set.uIcc_of_le zero_le_one] using member)
  have path_continuous : Continuous path := by fun_prop
  have integrable : IntervalIntegrable (fun parameter : ℝ => (point - Complex.I) *
      functional (classicalBinaryForm form degree (path parameter))) volume 0 1 :=
    (continuousOn_const.mul ((classicalBinaryForm_coord_holomorphic form degree functional).continuousOn.comp
      path_continuous.continuousOn image)).intervalIntegrable
  have derivative (parameter : ℝ) (member : parameter ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun parameter : ℝ => functional (classicalBinaryPrimitive form degree (path parameter)))
        ((point - Complex.I) * functional (classicalBinaryForm form degree (path parameter))) parameter := by
    have outer := (classicalBinaryPrimitive_hasDerivAt form degree functional
      (path parameter) (image parameter member)).hasFDerivAt.restrictScalars ℝ
    have inner : HasDerivAt path (point - Complex.I) parameter := by
      simpa only [path, Complex.real_smul, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
        ((Complex.ofRealCLM.hasDerivAt.mul_const (point - Complex.I)).const_add Complex.I)
    exact outer.comp_hasDerivAt parameter inner
  have result := (intervalIntegral.integral_eq_sub_of_hasDerivAt derivative integrable).symm
  simpa only [path, zero_smul, add_zero, one_smul, add_sub_cancel,
    classicalBinaryPrimitive_basepoint, map_zero, sub_zero] using result

end TernaryPeriodPolynomials.SphericalDetection.Helpers
