module

public import TernaryPeriodPolynomials.DifferentialForm.AdjointExtensionFormula
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientExtension
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Formula
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.CutoffConvolutionBound

@[expose] public section


/-! Actual fixed-scale adjoint component bounds with every metric coefficient extended legitimately. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive CompactCoordinateIntegration
open scoped ContDiff

theorem exists_mollifiedChart_adjoint_component_bound (n k : ℕ) (S : Space)
    (χ η : Coordinates → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ (quotientChart S).target) (c : ℝ) (hc : c ≠ 0) (i : Index n k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EquivariantForm (deckRepresentation n) univ (k+1),
      ∫ x, ‖components n k (localAdjoint n k (mollifiedChartRaw n (k+1) S χ η c w)) i x‖^2 ≤
        C * ∑ t, ∫ x, ‖components n (k+1) (cutoffChartRaw n (k+1) S χ w) t x‖^2 := by
  obtain ⟨a,b,_,_,_,hab,he⟩ := exists_adjoint_coefficient_extensions n k hcη
    (hsη.trans (quotientChart_target_subset S))
  obtain ⟨C,hC,hbound⟩ := exists_matrix_cutoff_convolution_bound volume
    (fun q : Index n k × Index n (k+1) × Fin 5 => (Pi.single q.2.2 1 : Coordinates))
    (CompactScalarMollifier.kernel Coordinates volume c) η
    (fun i t q => a i t q.1 q.2.1 q.2.2) (fun i t q => b i t q.1 q.2.1 q.2.2)
    ((CompactScalarMollifier.kernel_contDiff Coordinates volume c).of_le (by simp))
    (CompactScalarMollifier.kernel_compact Coordinates volume c hc) (hη.of_le (by simp)) hcη
    (fun i t q => (hab i t q.1 q.2.1 q.2.2).1.continuous)
    (fun i t q => (hab i t q.1 q.2.1 q.2.2).2.1.continuous) i
  refine ⟨C,hC,fun w => ?_⟩
  have hcomp : components n (k+1) (mollifiedChartRaw n (k+1) S χ η c w) =
      (fun t y => η y * scalarConvolution volume (CompactScalarMollifier.kernel Coordinates volume c)
        (components n (k+1) (cutoffChartRaw n (k+1) S χ w) t) y) :=
    funext (fun t => funext (components_mollifiedChartRaw n (k+1) S χ η c w t))
  have hlocal := localAdjoint_eq_extended_matrix n k (tsupport η)
    (hsη.trans (quotientChart_target_subset S)) a b
    (fun x hx i t l j d => ⟨(he x hx i t l j d).1.self_of_nhds, (he x hx i t l j d).2.self_of_nhds⟩)
    (mollifiedChartRaw n (k+1) S χ η c w)
    (contDiff_mollifiedChartRaw n (k+1) S χ η c hc hχ hsχ hη w)
    (tsupport_mollifiedChartRaw n (k+1) S χ η c w) i
  have h := hbound (components n (k+1) (cutoffChartRaw n (k+1) S χ w))
    (fun t => (contDiff_cutoffChartComponents n (k+1) S χ hχ hsχ w t).continuous)
    (fun t => compact_cutoffChartComponents n (k+1) S χ hcχ w t)
  rw [hcomp] at hlocal
  exact (congrArg (fun f : Coordinates → ℝ => ∫ x, ‖f x‖^2) hlocal).le.trans h

end TernaryPoly.PolynomialFormCoordinates
