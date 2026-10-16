module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.InputBound
public import TernaryPeriodPolynomials.DifferentialForm.Chart.OutputBound
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Regularizer
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! A genuine uniform Hilbert bound for the actual compact chart regularizer. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)

include hcχ in
theorem exists_chart_regularizer_square_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, ∀ hc : 0 < c, ∀ w : Core n k,
      ‖inclusion n k (chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val)‖^2 ≤
        C * ‖inclusion n k w‖^2 := by
  have HI := exists_chart_input_bound n k S χ hχ hcχ hsχ
  have HO := exists_chart_output_bound n k S χ η hχ hcχ hsχ hη hcη hsη
  let D : ℝ := HI.choose
  let B : ℝ := HO.choose
  have hD : 0 ≤ D := HI.choose_spec.1
  have hB : 0 ≤ B := HO.choose_spec.1
  refine ⟨B*D,mul_nonneg hB hD,fun c hc w => ?_⟩
  exact (HO.choose_spec.2 c hc w.val).trans
    ((mul_le_mul_of_nonneg_left (HI.choose_spec.2 w) hB).trans_eq (mul_assoc B D _).symm)

include hcχ in
theorem exists_chart_regularizer_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, ∀ hc : 0 < c, ∀ w : Core n k,
      ‖inclusion n k (chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val)‖ ≤
        C * ‖inclusion n k w‖ := by
  have H := exists_chart_regularizer_square_bound n k S χ η hχ hcχ hsχ hη hcη hsη
  let C : ℝ := H.choose
  have hC : 0 ≤ C := H.choose_spec.1
  refine ⟨Real.sqrt C,Real.sqrt_nonneg C,fun c hc w => ?_⟩
  have he := Real.sq_sqrt hC
  have hh := H.choose_spec.2 c hc w
  have hp := mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (inclusion n k w))
  nlinarith [sq_nonneg (‖inclusion n k (chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w.val)‖ -
    Real.sqrt C * ‖inclusion n k w‖)]

end TernaryPoly.PolynomialFormCoordinates
