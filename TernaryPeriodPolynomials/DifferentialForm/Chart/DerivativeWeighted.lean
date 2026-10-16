module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.DerivativeComponents
public import TernaryPeriodPolynomials.DifferentialForm.WeightedCoordinateUpper
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Linear

@[expose] public section


/-! Fixed-scale weighted energy bound for the actual chart exterior derivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham SmoothLocalDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff

theorem exists_mollifiedChart_derivative_weighted_bound (n k : ℕ) (S : Space)
    (χ η : Coordinates → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target) (c : ℝ) (hc : c ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EquivariantForm (deckRepresentation n) univ k,
      ∫ x, weightedSquare n (k+1) (extDeriv (mollifiedChartRaw n k S χ η c w)) x ≤
        C * ∑ i, ∫ x, ‖components n k (cutoffChartRaw n k S χ w) i x‖^2 := by
  classical
  have hcomp := fun j => exists_mollifiedChart_derivative_component_bound n k S χ η hχ hcχ hsχ hη hcη c hc j
  choose A hA hbound using hcomp
  obtain ⟨B,hB,hweighted⟩ := exists_compact_weighted_coordinate_upper n (k+1) hcη
    (hsη.trans (quotientChart_target_subset S))
  refine ⟨B * ∑ j, A j, mul_nonneg hB (Finset.sum_nonneg (fun j _ => hA j)), ?_⟩
  intro w
  let d := extDeriv (mollifiedChartRaw n k S χ η c w)
  have hd : ContDiff ℝ ∞ d := contDiffOn_univ.mp
    (smooth_extDeriv isOpen_univ (contDiff_mollifiedChartRaw n k S χ η c hc hχ hsχ hη w).contDiffOn)
  have hs : tsupport d ⊆ tsupport η :=
    (tsupport_extDeriv_subset n k (mollifiedChartRaw n k S χ η c w)).trans
      (tsupport_mollifiedChartRaw n k S χ η c w)
  have hw := hweighted d hd (hcη.of_isClosed_subset (isClosed_tsupport _) hs) hs
  exact hw.trans ((mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hbound j w)) hB).trans_eq
    (by rw [← Finset.sum_mul, ← mul_assoc]))

end TernaryPoly.PolynomialFormCoordinates
