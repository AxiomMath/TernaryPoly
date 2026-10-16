module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.OuterValues
public import Mathlib.NumberTheory.ModularForms.LFunction

@[expose] public section


open Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem levelOneCuspForm_LSeries_eq_L {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (argument : ℂ) (convergent : (weight : ℝ) / 2 + 1 < argument.re) :
    LSeries (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) argument =
      ModularForm.L positive form argument := by
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  have zero := CuspFormClass.qExpansion_coeff_zero form (by norm_num : (0 : ℝ) < 1) period
  have summed := CuspForm.hasSum_L positive form convergent
  simp only [Subgroup.strictWidthInfty_SL2Z, Complex.ofReal_one, Complex.one_cpow, one_mul] at summed
  have terms : LSeries.term (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) argument =
      fun index => (UpperHalfPlane.qExpansion 1 form).coeff index / (index : ℂ) ^ argument := by
    funext index
    rw [LSeries.term_def]
    split_ifs with is_zero
    · subst index
      simp only [zero, zero_div]
    · rfl
  change (∑' index, LSeries.term (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) argument index) = _
  rw [terms]
  exact summed.tsum_eq

theorem levelOneCuspForm_mellin_ne_zero {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (argument : ℂ) (convergent : (weight : ℝ) / 2 + 1 < argument.re)
    (nonzero : LSeries (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) argument ≠ 0) :
    mellin (fun height => form (UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)))) argument ≠ 0 := by
  rw [levelOneCuspForm_LSeries_eq_L positive form argument convergent] at nonzero
  intro zero
  apply nonzero
  rw [ModularForm.L, CuspForm.Λ_eq_mellin, zero]
  simp

def cuspImaginaryMoment {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight) (power : ℕ) : ℂ :=
  ∫ height : ℝ in Set.Ioi 0, (height : ℂ) ^ power *
    form (UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)))

theorem cuspImaginaryMoment_eq_mellin {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight) (power : ℕ) :
    cuspImaginaryMoment form power =
      mellin (fun height => form (UpperHalfPlane.ofComplex (Complex.I * (height : ℂ)))) ((power : ℂ) + 1) := by
  simp only [cuspImaginaryMoment, mellin, add_sub_cancel_right, Complex.cpow_natCast, smul_eq_mul]

theorem cuspImaginaryMoment_ne_zero {weight : ℤ} (positive : 0 < weight)
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (power : ℕ) (convergent : (weight : ℝ) / 2 + 1 < (power : ℝ) + 1)
    (nonzero : LSeries (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) ((power : ℂ) + 1) ≠ 0) :
    cuspImaginaryMoment form power ≠ 0 := by
  rw [cuspImaginaryMoment_eq_mellin]
  exact levelOneCuspForm_mellin_ne_zero positive form _ (by simpa using convergent) nonzero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
