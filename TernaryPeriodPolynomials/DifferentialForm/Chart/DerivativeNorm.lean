module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.DerivativeWeighted
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential
public import TernaryPeriodPolynomials.DifferentialForm.Chart.HilbertNorm
public import TernaryPeriodPolynomials.DifferentialForm.Chart.InputBound

@[expose] public section

/-! Actual fixed-scale Hilbert bound for compact differential after chart regularization. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

theorem norm_chartMollifier_differential_square (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    ‖inclusion n (k+1) (compactDifferential (deckRepresentation n) isOpen_univ k
      (chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w))‖^2 =
      ∫ x, weightedSquare n (k+1) (extDeriv (mollifiedChartRaw n k S χ η c w)) x := by
  let a := chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w
  have hs := quotientSupport_chartMollifier_source n k S χ η c hc hχ hsχ hη hcη hsη w
  have hn := norm_inclusion_square_chart n (k+1) S
    (compactDifferential (deckRepresentation n) isOpen_univ k a)
    ((quotientSupport_differential isOpen_univ a.val).trans hs)
  have he := (globalChartRepresentative_compactDifferential n k S a hs).trans
    (congrArg extDeriv (globalChartRepresentative_chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w))
  exact hn.trans (congrArg (fun z : Coordinates → FormValue n (k+1) => ∫ x, weightedSquare n (k+1) z x) he)

theorem exists_chart_differential_square_bound (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : c ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Core n k,
      ‖inclusion n (k+1) (compactDifferential (deckRepresentation n) isOpen_univ k
        (chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w.val))‖^2 ≤ C * ‖inclusion n k w‖^2 := by
  have HI := exists_chart_input_bound n k S χ hχ hcχ hsχ
  have HO := exists_mollifiedChart_derivative_weighted_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc
  let A : ℝ := HI.choose
  let B : ℝ := HO.choose
  have hA : 0 ≤ A := HI.choose_spec.1
  have hB : 0 ≤ B := HO.choose_spec.1
  refine ⟨B*A,mul_nonneg hB hA,fun w => ?_⟩
  exact (norm_chartMollifier_differential_square n k S χ η c hc hχ hsχ hη hcη hsη w.val).le.trans
    ((HO.choose_spec.2 w.val).trans ((mul_le_mul_of_nonneg_left (HI.choose_spec.2 w) hB).trans_eq (mul_assoc B A _).symm))

end TernaryPoly.PolynomialFormCoordinates
