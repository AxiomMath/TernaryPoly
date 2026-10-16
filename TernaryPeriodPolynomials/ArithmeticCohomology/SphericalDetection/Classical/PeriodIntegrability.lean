module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.BinaryCocycle
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section


open GeneralEisenstein Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspImaginaryMoment_integrable {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight) (power : ℕ) :
    IntegrableOn (fun height : ℝ => (height : ℂ) ^ power *
      form (UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)))) (Set.Ioi 0) := by
  have mellin := ((CuspForm.isStrongFEPair positive form).hasMellin ((power : ℂ) + 1)).1
  simpa only [MellinConvergent, add_sub_cancel_right, Complex.cpow_natCast,
    ModularForm.weakFEPair_f, smul_eq_mul] using mellin

theorem classicalBinaryForm_coord_imaginary_integrable {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (position : Fin (degree + 1)) :
    IntegrableOn (fun height : ℝ =>
      (binaryStandardBasis degree).coord position (classicalBinaryForm form degree (Complex.I * (height : ℂ))) *
        Complex.I) (Set.Ioi 0) := by
  have integrable := (cuspImaginaryMoment_integrable positive form (degree - position.val)).const_mul
    ((degree.choose position.val : ℂ) * (-Complex.I) ^ (degree - position.val) * Complex.I)
  apply integrable.congr
  filter_upwards [] with height
  simp only [classicalBinaryForm, map_smul, smul_eq_mul, binaryPointPower_standardCoord,
    ← neg_mul, mul_pow]
  ring

theorem binaryStandardBasis_functional (degree : ℕ)
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) (polynomial : Binary.HomogeneousPoly degree) :
    functional polynomial = ∑ position : Fin (degree + 1),
      (binaryStandardBasis degree).coord position polynomial * functional (binaryStandardBasis degree position) := by
  conv_lhs => rw [← (binaryStandardBasis degree).sum_repr polynomial]
  simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]

theorem classicalBinaryForm_imaginary_integrable {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    IntegrableOn (fun height : ℝ => functional (classicalBinaryForm form degree (Complex.I * (height : ℂ))) *
      Complex.I) (Set.Ioi 0) := by
  have integrable := integrable_finsetSum Finset.univ (fun position _ =>
    (classicalBinaryForm_coord_imaginary_integrable positive form degree position).mul_const
      (functional (binaryStandardBasis degree position)))
  apply integrable.congr
  filter_upwards [] with height
  rw [binaryStandardBasis_functional degree functional, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro position _
  ring

theorem cuspPeriodPolynomial_functional_integral {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    functional (cuspPeriodPolynomial form degree) =
      ∫ height : ℝ in Set.Ioi 0,
        functional (classicalBinaryForm form degree (Complex.I * (height : ℂ))) * Complex.I := by
  rw [binaryStandardBasis_functional degree functional]
  have coordinates (position : Fin (degree + 1)) :
      (binaryStandardBasis degree).coord position (cuspPeriodPolynomial form degree) =
        ∫ height : ℝ in Set.Ioi 0,
          (binaryStandardBasis degree).coord position (classicalBinaryForm form degree (Complex.I * (height : ℂ))) *
            Complex.I := by
    rw [cuspPeriodPolynomial_coord_integral]
    apply integral_congr_ae
    filter_upwards [] with height
    simp only [classicalBinaryForm, map_smul, smul_eq_mul]
    ring
  simp only [coordinates, ← integral_mul_const]
  rw [← integral_finsetSum _ (fun position _ =>
    (classicalBinaryForm_coord_imaginary_integrable positive form degree position).mul_const
      (functional (binaryStandardBasis degree position)))]
  apply integral_congr_ae
  filter_upwards [] with height
  rw [binaryStandardBasis_functional degree functional, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro position _
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
