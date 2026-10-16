module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Codifferential.ComponentConvergence
public import TernaryPeriodPolynomials.DifferentialForm.Chart.CoordinateConvergence

@[expose] public section

/-! Strong convergence of the actual compact codifferential chart commutator. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff Topology

theorem coreChartCodifferentialCommutator_tendsto (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : Core n (k+1)) :
    Tendsto (fun j : ℕ => inclusion n k
      (coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) w))
      atTop (nhds (inclusion n k (coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w))) := by
  let a (j : ℕ) := coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη
    ((j:ℝ)+1) (by positivity) w
  let b := coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w
  let e (j : ℕ) : Core n k := a j - b
  have hs (j : ℕ) : quotientSupport (e j).val ⊆ (quotientChart S).symm '' tsupport η :=
    (quotientSupport_sub (a j).val b.val).trans (union_subset
      (quotientSupport_coreChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη
        ((j:ℝ)+1) (by positivity) w)
      (quotientSupport_coreChartCodifferentialLimit n k S χ η hχ hη hcη hsη w))
  have hz := chart_supported_inclusion_tendsto_zero n k S (tsupport η) hcη hsη e hs
    (codifferentialCommutator_component_tendsto n k S χ η hχ hcχ hsχ hη hcη hsη w)
  have hsum : Tendsto (fun j : ℕ => inclusion n k (e j) + inclusion n k b)
      atTop (nhds (inclusion n k b)) := by
    simpa only [zero_add] using hz.add_const (inclusion n k b)
  exact hsum.congr (fun j =>
    (congrArg (fun z : Hilbert n k => z + inclusion n k b)
      ((inclusion n k).map_sub (a j) b)).trans (sub_add_cancel _ _))

end TernaryPoly.PolynomialFormCoordinates
