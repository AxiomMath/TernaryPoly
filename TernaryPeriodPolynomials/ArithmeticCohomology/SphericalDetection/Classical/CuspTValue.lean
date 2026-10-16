module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.HorizontalDecay

@[expose] public section


open GeneralEisenstein Matrix MeasureTheory Filter
open scoped Topology

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem classicalBinaryPrimitive_horizontal_integral {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (height : ℝ) (positive : 0 < height) :
    functional (classicalBinaryPrimitive form degree (1 + Complex.I * (height : ℂ))) -
        functional (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ))) =
      ∫ horizontal : ℝ in 0..1,
        functional (classicalBinaryForm form degree ((horizontal : ℂ) + Complex.I * (height : ℂ))) := by
  have image (horizontal : ℝ) : (horizontal : ℂ) + Complex.I * (height : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa using positive
  have path : Continuous (fun horizontal : ℝ => (horizontal : ℂ) + Complex.I * (height : ℂ)) := by fun_prop
  have integrable : IntervalIntegrable (fun horizontal : ℝ =>
      functional (classicalBinaryForm form degree ((horizontal : ℂ) + Complex.I * (height : ℂ)))) volume 0 1 :=
    ((classicalBinaryForm_coord_holomorphic form degree functional).continuousOn.comp
      path.continuousOn (fun horizontal _ => image horizontal)).intervalIntegrable
  have derivative (horizontal : ℝ) (_member : horizontal ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun horizontal : ℝ => functional
        (classicalBinaryPrimitive form degree ((horizontal : ℂ) + Complex.I * (height : ℂ))))
        (functional (classicalBinaryForm form degree ((horizontal : ℂ) + Complex.I * (height : ℂ)))) horizontal := by
    have outer := (classicalBinaryPrimitive_hasDerivAt form degree functional
      ((horizontal : ℂ) + Complex.I * (height : ℂ)) (image horizontal)).hasFDerivAt.restrictScalars ℝ
    have inner : HasDerivAt (fun horizontal : ℝ => (horizontal : ℂ) + Complex.I * (height : ℂ)) 1 horizontal :=
      Complex.ofRealCLM.hasDerivAt.add_const _
    convert outer.comp_hasDerivAt horizontal inner using 1
    all_goals first | rfl | simp [ContinuousLinearMap.toSpanSingleton_apply]
  simpa only [Complex.ofReal_one, Complex.ofReal_zero, zero_add] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt derivative integrable).symm

theorem classicalBinaryPrimitive_horizontal_difference_tendsto {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (position : Fin (degree + 1)) :
    Tendsto (fun height : ℝ =>
      (binaryStandardBasis degree).coord position (classicalBinaryPrimitive form degree (1 + Complex.I * (height : ℂ))) -
        (binaryStandardBasis degree).coord position (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ))))
      atTop (𝓝 0) := by
  apply (classicalBinaryForm_coord_horizontal_integral_tendsto form degree position).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with height positive
  exact (classicalBinaryPrimitive_horizontal_integral form degree ((binaryStandardBasis degree).coord position)
    height positive).symm

theorem modularT_imaginary (height : ℝ) (positive : 0 < height) :
    ((SpecialLinearGroup.mapGL ℝ ModularGroup.T •
      UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)) : UpperHalfPlane) : ℂ) =
        1 + Complex.I * (height : ℂ) := by
  let point : UpperHalfPlane := ⟨Complex.I * (height : ℂ), by simpa using positive⟩
  have point_eq : UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)) = point :=
    UpperHalfPlane.ofComplex_apply point
  rw [point_eq]
  change ((ModularGroup.T • point : UpperHalfPlane) : ℂ) = _
  rw [UpperHalfPlane.modular_T_smul]
  simp [point, add_comm]

theorem cuspNormalizedBinaryCocycle_T {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ) :
    cuspNormalizedBinaryCocycle form degree weight_eq twist ModularGroup.T = 0 := by
  let action : Module.End ℂ (Binary.HomogeneousPoly degree) :=
    (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL ModularGroup.T)
  let value : Binary.HomogeneousPoly degree := classicalBinaryCocycle form degree weight_eq twist ModularGroup.T
  apply (binaryStandardBasis degree).ext_elem
  intro position
  let functional := (binaryStandardBasis degree).coord position
  have source_limit := classicalBinaryPrimitive_tendsto_atTop positive form degree functional
  have translated_limit := (classicalBinaryPrimitive_tendsto_atTop positive form degree (functional.comp action)).const_add
    (functional value)
  have difference_limit := translated_limit.sub source_limit
  have same : (fun height : ℝ => functional value + (functional.comp action)
      (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ))) -
        functional (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ)))) =ᶠ[atTop]
      (fun height : ℝ => functional (classicalBinaryPrimitive form degree (1 + Complex.I * (height : ℂ))) -
        functional (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with height height_positive
    let point : UpperHalfPlane := ⟨Complex.I * (height : ℂ), by simpa using height_positive⟩
    have relation := congrArg functional (classicalBinaryPrimitive_modular form degree weight_eq twist ModularGroup.T point)
    have point_eq : UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)) = point :=
      UpperHalfPlane.ofComplex_apply point
    have translated : ((SpecialLinearGroup.mapGL ℝ ModularGroup.T • point : UpperHalfPlane) : ℂ) =
        1 + Complex.I * (height : ℂ) := by simpa only [point_eq] using modularT_imaginary height height_positive
    rw [translated, map_sub] at relation
    change functional (classicalBinaryPrimitive form degree (1 + Complex.I * (height : ℂ))) - functional value =
      (functional.comp action) (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ))) at relation
    linear_combination -relation
  have equal := tendsto_nhds_unique (difference_limit.congr' same)
    (classicalBinaryPrimitive_horizontal_difference_tendsto form degree position)
  change functional (value + (action (classicalBinaryCuspConstant form degree) - classicalBinaryCuspConstant form degree)) = 0
  rw [map_add, map_sub]
  change functional value + (functional (action (classicalBinaryCuspConstant form degree)) -
    functional (classicalBinaryCuspConstant form degree)) = 0
  change functional value + functional (action (classicalBinaryCuspConstant form degree)) -
    functional (classicalBinaryCuspConstant form degree) = 0 at equal
  linear_combination equal

end TernaryPeriodPolynomials.SphericalDetection.Helpers
