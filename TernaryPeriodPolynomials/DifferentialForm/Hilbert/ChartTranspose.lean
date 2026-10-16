module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.TransposePairing
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Regularizer
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section


/-! The actual Hilbert chart adjoint maps every compact test to the proved compact transpose. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : 0 < c)

theorem inner_hilbertChartRegularizer_transpose (x : Hilbert n k) (b : Core n k) :
    inner ℝ (hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc x) (inclusion n k b) =
      inner ℝ (x) (inclusion n k (chartTranspose n k S χ η c hc.ne' hχ hcχ hsχ hη hsη b.val)) := by
  let R := hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc
  refine (inclusion_dense n k).induction_on x ?_ ?_
  · exact isClosed_eq (R.continuous.inner continuous_const) (continuous_id.inner continuous_const)
  intro a
  exact (congrArg (fun z : Hilbert n k => inner ℝ z (inclusion n k b))
    (hilbertChartRegularizer_inclusion n k S χ η hχ hcχ hsχ hη hcη hsη c hc a)).trans
      (inner_chartMollifier_transpose n k S χ η c hc.ne' hχ hcχ hsχ hη hcη hsη a b)

theorem hilbertChartRegularizer_adjoint_inclusion (b : Core n k) :
    (hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc).adjoint (inclusion n k b) =
      inclusion n k (chartTranspose n k S χ η c hc.ne' hχ hcχ hsχ hη hsη b.val) := by
  apply ext_inner_left ℝ
  intro x
  exact (ContinuousLinearMap.adjoint_inner_right _ x (inclusion n k b)).trans
    (inner_hilbertChartRegularizer_transpose n k S χ η hχ hcχ hsχ hη hcη hsη c hc x b)

end TernaryPoly.PolynomialFormCoordinates
