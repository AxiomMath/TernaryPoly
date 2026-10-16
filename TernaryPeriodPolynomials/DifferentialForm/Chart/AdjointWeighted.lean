module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.AdjointComponents
public import TernaryPeriodPolynomials.DifferentialForm.WeightedCoordinateUpper

@[expose] public section


/-! Fixed-scale weighted energy bounds for the genuine chart codifferential. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff

theorem exists_mollifiedChart_adjoint_weighted_bound (n k : ℕ) (S : Space)
    (χ η : Coordinates → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target) (c : ℝ) (hc : c ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EquivariantForm (deckRepresentation n) univ (k+1),
      ∫ x, weightedSquare n k (localAdjoint n k (mollifiedChartRaw n (k+1) S χ η c w)) x ≤
        C * ∑ t, ∫ x, ‖components n (k+1) (cutoffChartRaw n (k+1) S χ w) t x‖^2 := by
  classical
  have hcomp := fun i => exists_mollifiedChart_adjoint_component_bound n k S χ η hχ hcχ hsχ hη hcη hsη c hc i
  choose A hA hbound using hcomp
  obtain ⟨B,hB,hweighted⟩ := exists_compact_weighted_coordinate_upper n k hcη
    (hsη.trans (quotientChart_target_subset S))
  refine ⟨B * ∑ i, A i, mul_nonneg hB (Finset.sum_nonneg (fun i _ => hA i)), ?_⟩
  intro w
  let f := mollifiedChartRaw n (k+1) S χ η c w
  let d := localAdjoint n k f
  have hfs : tsupport f ⊆ tsupport η := tsupport_mollifiedChartRaw n (k+1) S χ η c w
  have hd : ContDiff ℝ ∞ d := contDiff_localAdjoint n k
    (contDiff_mollifiedChartRaw n (k+1) S χ η c hc hχ hsχ hη w).contDiffOn
    (hfs.trans (hsη.trans (quotientChart_target_subset S)))
  have hs : tsupport d ⊆ tsupport η := (tsupport_localAdjoint n k f).trans hfs
  have hw := hweighted d hd (hcη.of_isClosed_subset (isClosed_tsupport _) hs) hs
  exact hw.trans ((mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hbound i w)) hB).trans_eq
    (by rw [← Finset.sum_mul, ← mul_assoc]))

end TernaryPoly.PolynomialFormCoordinates
