module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.ComponentCutoffs
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Transpose

@[expose] public section


noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive CompactCoordinateIntegration
open scoped ContDiff

theorem integral_chartMollifier_transpose (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (a b : EquivariantForm (deckRepresentation n) univ k) :
    ∫ x, weightedPairing (weightedGram n k) (components n k (mollifiedChartRaw n k S χ η c a))
      (components n k (globalChartRepresentative (deckRepresentation n) S k b).val) x =
    ∫ x, weightedPairing (weightedGram n k)
      (components n k (globalChartRepresentative (deckRepresentation n) S k a).val)
      (components n k (chartTransposeRaw n k S χ η c b)) x := by
  let f := components n k (globalChartRepresentative (deckRepresentation n) S k a).val
  let g := components n k (globalChartRepresentative (deckRepresentation n) S k b).val
  have hf (i : Index n k) : (fun x => χ x * f i x) = components n k (cutoffChartRaw n k S χ a) i :=
    funext (fun x => (components_cutoffChartRaw n k S χ a i x).symm)
  have h := integral_weightedCutoffTranspose volume (weightedGram n k)
    (CompactScalarMollifier.kernel Coordinates volume c) χ η
    (fun x hx => isUnit_iff_ne_zero.mpr (ne_of_gt (weightedGram_posDef n k x
      (quotientChart_target_subset S (hsχ hx))).det_pos))
    ((CompactScalarMollifier.kernel_contDiff Coordinates volume c).of_le (by simp))
    (CompactScalarMollifier.kernel_compact Coordinates volume c hc) f g
    (fun i => (hf i).symm ▸ (contDiff_cutoffChartComponents n k S χ hχ hsχ a i).continuous)
    (fun i => (hf i).symm ▸ compact_cutoffChartComponents n k S χ hcχ a i)
    (fun i => (contDiff_chartDualInput n k S η hη hsη b i).continuous)
    (fun i => compact_chartDualInput n k S η hcη b i)
  rw [components_mollifiedChartRaw_eq_cutoffConvolution, components_chartTransposeRaw]
  exact h

end TernaryPoly.PolynomialFormCoordinates
