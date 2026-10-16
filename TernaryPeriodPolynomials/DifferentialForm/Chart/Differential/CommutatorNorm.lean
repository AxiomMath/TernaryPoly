module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential.CommutatorBound
public import TernaryPeriodPolynomials.DifferentialForm.Chart.SupportedNorm
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section


/-! One genuine Hilbert norm bound controls the actual differential chart commutators at all positive scales. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)

theorem exists_differentialCommutator_square_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (hc : 0 < c) (w : Core n k),
      ‖inclusion n (k+1) (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)‖^2 ≤
        C * ‖inclusion n k w‖^2 := by
  classical
  have H := fun i => exists_differentialCommutator_component_bound n k S χ η hχ hcχ hsχ hη hcη hsη i
  let A : Index n (k+1) → ℝ := fun i => (H i).choose
  have hA (i : Index n (k+1)) : 0 ≤ A i := (H i).choose_spec.1
  have HB := exists_chart_supported_norm_bound n (k+1) S (tsupport η) hcη hsη
  let B : ℝ := HB.choose
  have hB : 0 ≤ B := HB.choose_spec.1
  refine ⟨B * ∑ i, A i, mul_nonneg hB (Finset.sum_nonneg (fun i _ => hA i)),fun c hc w => ?_⟩
  have hb := HB.choose_spec.2
    (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)
    (quotientSupport_coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (H i).choose_spec.2 c hc w)
  have halg (N : ℝ) : B * (∑ i, A i * N) = (B * ∑ i, A i) * N := by
    rw [← Finset.sum_mul, ← mul_assoc]
  exact hb.trans ((mul_le_mul_of_nonneg_left hs hB).trans_eq (halg _))

theorem exists_differentialCommutator_norm_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (hc : 0 < c) (w : Core n k),
      ‖inclusion n (k+1) (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc w)‖ ≤
        C * ‖inclusion n k w‖ := by
  have H := exists_differentialCommutator_square_bound n k S χ η hχ hcχ hsχ hη hcη hsη
  let C : ℝ := H.choose
  have hC : 0 ≤ C := H.choose_spec.1
  refine ⟨Real.sqrt C,Real.sqrt_nonneg C,fun c hc w => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (inclusion n k w)))).mp
  simpa only [mul_pow, Real.sq_sqrt hC] using H.choose_spec.2 c hc w

end TernaryPoly.PolynomialFormCoordinates
