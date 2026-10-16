module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Square
public import TernaryPeriodPolynomials.DifferentialForm.Chart.HilbertNorm
public import TernaryPeriodPolynomials.DifferentialForm.WeightedSquare
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Bound
public import TernaryPeriodPolynomials.DifferentialForm.Chart.NormFormulas

@[expose] public section


/-! Uniform true quotient Hilbert-norm control of the actual chart mollifier output. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
  SymmetricSpaceRiemannian PolynomialFormHilbert
open scoped ContDiff

theorem exists_chart_output_bound (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : ℝ, ∀ hc : 0 < c,
      ∀ w : EquivariantForm (deckRepresentation n) univ k,
      ‖inclusion n k (chartMollifier n k S χ η c hc.ne' hχ hsχ hη hcη hsη w)‖^2 ≤
        B * ∑ i, ∫ x, ‖components n k (cutoffChartRaw n k S χ w) i x‖^2 := by
  have HM := CompactScalarBound.exists_bound η hη.continuous hcη
  let M : ℝ := HM.choose
  have hM : 0 ≤ M := HM.choose_spec.1
  have hMb : ∀ x, ‖η x‖ ≤ M := HM.choose_spec.2
  have H : ∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧ ∀ f : Coordinates → FormValue n k,
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ tsupport η →
      d * (∫ x, ‖f x‖^2) ≤ ∫ x, weightedSquare n k f x ∧
      (∫ x, weightedSquare n k f x) ≤ C * ∫ x, ‖f x‖^2 := by
    convert! compact_integral_weighted_bounds n k (K := tsupport η) hcη
      (hsη.trans (quotientChart_target_subset S)) using 1
  let C : ℝ := H.choose_spec.choose
  have hC : 0 ≤ C := H.choose_spec.choose_spec.2.1
  have hb := H.choose_spec.choose_spec.2.2
  let A := ‖(coordinates n k).symm.toContinuousLinearMap‖^2 * M^2
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨C*A,mul_nonneg hC hA,fun c hc w => ?_⟩
  let f := mollifiedChartRaw n k S χ η c w
  have hn := norm_chartMollifier_eq_weightedSquare n k S χ η c hc.ne' hχ hsχ hη hcη hsη w
  have hf := contDiff_mollifiedChartRaw n k S χ η c hc.ne' hχ hsχ hη w
  have hcf : HasCompactSupport f := hcη.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_mollifiedChartRaw n k S χ η c w)
  have hu := (hb f hf hcf (tsupport_mollifiedChartRaw n k S χ η c w)).2
  have hcoord := mollifiedChartRaw_square_bound n k S χ η hχ hcχ hsχ hη hcη M hM hMb c hc w
  exact hn.le.trans (hu.trans ((mul_le_mul_of_nonneg_left hcoord hC).trans_eq
    (mul_assoc C A _).symm))

end TernaryPoly.PolynomialFormCoordinates
