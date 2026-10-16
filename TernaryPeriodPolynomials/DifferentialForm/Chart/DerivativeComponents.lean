module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Formula
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.CutoffConvolutionBound

@[expose] public section


/-! Fixed-scale L2 bounds for the literal exterior derivative of the actual chart mollifier. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive CompactCoordinateIntegration
open scoped ContDiff

theorem exists_mollifiedChart_derivative_component_bound (n k : ℕ) (S : Space)
    (χ η : Coordinates → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (c : ℝ) (hc : c ≠ 0) (j : Index n (k+1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EquivariantForm (deckRepresentation n) univ k,
      ∫ x, ‖components n (k+1) (extDeriv (mollifiedChartRaw n k S χ η c w)) j x‖^2 ≤
        C * ∑ i, ∫ x, ‖components n k (cutoffChartRaw n k S χ w) i x‖^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_matrix_cutoff_convolution_bound volume
    (fun d : Fin 5 => (Pi.single d 1 : Coordinates))
    (CompactScalarMollifier.kernel Coordinates volume c) η
    (differentialCoefficients n k) (fun _ _ _ _ => 0)
    ((CompactScalarMollifier.kernel_contDiff Coordinates volume c).of_le (by simp))
    (CompactScalarMollifier.kernel_compact Coordinates volume c hc) (hη.of_le (by simp)) hcη
    (fun _ _ _ => continuous_const) (fun _ _ _ => continuous_const) j
  refine ⟨C,hC,fun w => ?_⟩
  have he : components n k (mollifiedChartRaw n k S χ η c w) =
      (fun i y => η y * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
        (components n k (cutoffChartRaw n k S χ w) i) y) :=
    funext (fun i => funext (components_mollifiedChartRaw n k S χ η c w i))
  have hd (x : Coordinates) := extDeriv_eq_matrixFirstOrder n k (mollifiedChartRaw n k S χ η c w)
    ((contDiff_mollifiedChartRaw n k S χ η c hc hχ hsχ hη w).differentiable (by simp) x) j
  have h := hbound (components n k (cutoffChartRaw n k S χ w))
    (fun i => (contDiff_cutoffChartComponents n k S χ hχ hsχ w i).continuous)
    (fun i => compact_cutoffChartComponents n k S χ hcχ w i)
  simp_rw [hd, he]
  exact h

end TernaryPoly.PolynomialFormCoordinates
