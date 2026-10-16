module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.LocalizationBound
public import TernaryPeriodPolynomials.DifferentialForm.Chart.HilbertNorm
public import TernaryPeriodPolynomials.DifferentialForm.WeightedSquare
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Norm
public import TernaryPeriodPolynomials.Analysis.Finite.CoordinateIntegral
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Bound
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Integral
public import TernaryPeriodPolynomials.DifferentialForm.Chart.NormFormulas

@[expose] public section

/-! Genuine quotient L2 control of every inner-cutoff chart component. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
  SymmetricSpaceRiemannian PolynomialFormHilbert CompactSquareIntegral
open scoped ContDiff

theorem exists_chart_input_bound (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : Core n k,
      (∑ i, ∫ x, ‖components n k (cutoffChartRaw n k S χ w.val) i x‖^2) ≤
        D * ‖inclusion n k w‖^2 := by
  have HM := CompactScalarBound.exists_bound χ hχ.continuous hcχ
  let M : ℝ := HM.choose
  have hMb : ∀ x, ‖χ x‖ ≤ M := HM.choose_spec.2
  have H : ∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧ ∀ f : Coordinates → FormValue n k,
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ tsupport χ →
      d * (∫ x, ‖f x‖^2) ≤ ∫ x, weightedSquare n k f x ∧
      (∫ x, weightedSquare n k f x) ≤ C * ∫ x, ‖f x‖^2 := by
    convert! compact_integral_weighted_bounds n k (K := tsupport χ) hcχ
      (hsχ.trans (quotientChart_target_subset S)) using 1
  let d : ℝ := H.choose
  have hd : 0 < d := H.choose_spec.choose_spec.1
  have hb := H.choose_spec.choose_spec.2.2
  let A : ℝ := (Fintype.card (Index n k) : ℝ) * ‖(coordinates n k).toContinuousLinearMap‖^2
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  refine ⟨A * (M^2/d), mul_nonneg hA (div_nonneg (sq_nonneg _) hd.le), fun w => ?_⟩
  let f := cutoffChartRaw n k S χ w.val
  have hf : ContDiff ℝ ∞ f := contDiff_cutoffChartRaw n k S χ hχ hsχ w.val
  have hcf : HasCompactSupport f := compact_cutoffChartRaw n k S χ hcχ w.val
  have hn := norm_chartCutoff_eq_weightedSquare n k S χ hχ hcχ hsχ w.val
  have hl := (hb f hf hcf (tsupport_cutoffChartRaw n k S χ w.val)).1
  have hu := norm_chartCutoff_square_le n k S χ hχ hcχ hsχ M hMb w
  have hbound : d * (∫ x, ‖f x‖^2) ≤ M^2 * ‖inclusion n k w‖^2 :=
    hl.trans (hn.symm.le.trans hu)
  have hi : (∫ x, ‖f x‖^2) ≤ M^2/d * ‖inclusion n k w‖^2 := by
    calc
      _ ≤ (M^2 * ‖inclusion n k w‖^2)/d :=
        (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hbound)
      _ = _ := by ring
  have hcoords := integral_components_le_norm n k f hf hcf
  exact hcoords.trans ((mul_le_mul_of_nonneg_left hi hA).trans_eq (mul_assoc _ _ _).symm)

end TernaryPoly.PolynomialFormCoordinates
