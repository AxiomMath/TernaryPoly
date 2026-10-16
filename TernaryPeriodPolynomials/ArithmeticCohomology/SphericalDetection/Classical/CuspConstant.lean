module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodIntegrability

@[expose] public section


open GeneralEisenstein Matrix MeasureTheory Filter
open scoped Topology

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def classicalBinaryCuspConstant {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) : Binary.HomogeneousPoly degree :=
  ∑ position : Fin (degree + 1),
    (∫ height : ℝ in Set.Ioi 1,
      (binaryStandardBasis degree).coord position (classicalBinaryForm form degree (Complex.I * (height : ℂ))) *
        Complex.I) • binaryStandardBasis degree position

theorem classicalBinaryCuspConstant_functional {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    functional (classicalBinaryCuspConstant form degree) =
      ∫ height : ℝ in Set.Ioi 1,
        functional (classicalBinaryForm form degree (Complex.I * (height : ℂ))) * Complex.I := by
  simp only [classicalBinaryCuspConstant, map_sum, map_smul, smul_eq_mul, ← integral_mul_const]
  rw [← integral_finsetSum _ (fun position _ =>
    ((classicalBinaryForm_coord_imaginary_integrable positive form degree position).mono_set
      (Set.Ioi_subset_Ioi zero_le_one)).mul_const (functional (binaryStandardBasis degree position)))]
  apply integral_congr_ae
  filter_upwards [] with height
  rw [binaryStandardBasis_functional degree functional, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro position _
  ring

theorem classicalBinaryPrimitive_eq_imaginary_integral {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (height : ℝ) (positive : 0 < height) :
    functional (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ))) =
      ∫ parameter : ℝ in 1..height,
        functional (classicalBinaryForm form degree (Complex.I * (parameter : ℂ))) * Complex.I := by
  simpa only [Complex.ofReal_one, mul_one, classicalBinaryPrimitive_basepoint, map_zero, sub_zero] using
    classicalBinaryPrimitive_imaginary_integral form degree functional 1 height (by norm_num) positive

theorem classicalBinaryPrimitive_tendsto_atTop {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    Tendsto (fun height : ℝ => functional (classicalBinaryPrimitive form degree (Complex.I * (height : ℂ))))
      atTop (𝓝 (functional (classicalBinaryCuspConstant form degree))) := by
  rw [classicalBinaryCuspConstant_functional positive]
  have integrable := (classicalBinaryForm_imaginary_integrable positive form degree functional).mono_set
    (Set.Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))
  apply (intervalIntegral_tendsto_integral_Ioi 1 integrable tendsto_id).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with height height_positive
  exact (classicalBinaryPrimitive_eq_imaginary_integral form degree functional height height_positive).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
