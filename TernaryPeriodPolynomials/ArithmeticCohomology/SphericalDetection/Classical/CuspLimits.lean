module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CuspConstant

@[expose] public section


open GeneralEisenstein Matrix MeasureTheory Filter
open scoped Topology

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem positiveRay_primitive_tendsto_zero (function : ℝ → ℂ)
    (integrable : IntegrableOn function (Set.Ioi 0)) :
    Tendsto (fun height : ℝ => ∫ parameter : ℝ in 1..height, function parameter)
      (𝓝[Set.Ioi 0] 0)
      (𝓝 ((∫ parameter : ℝ in Set.Ioi 1, function parameter) -
        ∫ parameter : ℝ in Set.Ioi 0, function parameter)) := by
  let extension := (Set.Ioi (0 : ℝ)).indicator function
  have extension_integrable : Integrable extension := (integrable_indicator_iff measurableSet_Ioi).mpr integrable
  have continuous := intervalIntegral.continuous_primitive
    (fun lower upper => extension_integrable.intervalIntegrable (a := lower) (b := upper)) 0
  have small : Tendsto (fun height : ℝ => ∫ parameter : ℝ in 0..height, extension parameter)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    simpa using (continuous.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have limit := (tendsto_const_nhds (x := (∫ parameter : ℝ in Set.Ioi 1, function parameter) -
    ∫ parameter : ℝ in Set.Ioi 0, function parameter)).add small
  simp only [add_zero] at limit
  apply limit.congr'
  filter_upwards [self_mem_nhdsWithin] with height positive
  have integrable_one := integrable.mono_set (Set.Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))
  have integrable_height := integrable.mono_set (Set.Ioi_subset_Ioi positive.le)
  have one := intervalIntegral.integral_Ioi_sub_Ioi' integrable_one integrable_height
  have zero := intervalIntegral.integral_Ioi_sub_Ioi integrable positive.le
  have same : (∫ parameter : ℝ in 0..height, extension parameter) = ∫ parameter : ℝ in 0..height, function parameter := by
    rw [intervalIntegral.integral_of_le positive.le, intervalIntegral.integral_of_le positive.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro parameter member
    exact Set.indicator_of_mem member.1 function
  rw [same, ← one, ← zero]
  abel

theorem classicalBinaryPrimitive_tendsto_zero {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    Tendsto (fun height : ℝ => functional (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ))))
      (𝓝[Set.Ioi 0] 0)
      (𝓝 (functional (classicalBinaryCuspConstant form degree) - functional (cuspPeriodPolynomial form degree))) := by
  rw [classicalBinaryCuspConstant_functional positive, cuspPeriodPolynomial_functional_integral positive]
  apply (positiveRay_primitive_tendsto_zero _
    (classicalBinaryForm_imaginary_integrable positive form degree functional)).congr'
  filter_upwards [self_mem_nhdsWithin] with height height_positive
  exact (classicalBinaryPrimitive_eq_imaginary_integral form degree functional height height_positive).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
