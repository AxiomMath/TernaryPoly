module

public import TernaryPeriodPolynomials.DifferentialForm.JointGraph.Closure
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.GraphLimit
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartLimitUnique
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartDifferentialCommutatorLimit
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartCodifferentialCommutatorLimit
public import TernaryPeriodPolynomials.DifferentialForm.Chart.WeakTransport

@[expose] public section

/-! Every actual localized chart limit of a simultaneous weak graph input lies in the joint compact graph closure. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff Topology

attribute [local instance] PolynomialFormConnection.cutoffHilbertModule
attribute [local irreducible] maximalDifferential maximalCodifferential

theorem chartLimit_mem_jointGraphClosure (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (L : Hilbert n (k+1) →L[ℝ] Hilbert n (k+1))
    (hL : ∀ w : Core n (k+1), L (inclusion n (k+1) w) =
      inclusion n (k+1) (doubleChartCutoff n (k+1) S χ η hχ hη hcη hsη w.val))
    (x : Hilbert n (k+1)) (y : Hilbert n ((k+1)+1)) (z : Hilbert n k)
    (hy : (x,y) ∈ (maximalDifferential n (k+1)).graph)
    (hz : (x,z) ∈ (maximalCodifferential n k).graph) :
    ∃ v : Hilbert n ((k+1)+1), ∃ w : Hilbert n k, (L x,v,w) ∈ jointGraphClosure n k := by
  have HRd := exists_hilbertChartLimit n ((k+1)+1) S χ η hχ hcχ hsχ hη hcη hsη
  have HRa := exists_hilbertChartLimit n k S χ η hχ hcχ hsχ hη hcη hsη
  have HCd := exists_hilbertChartDifferentialCommutatorLimit n (k+1) S χ η hχ hcχ hsχ hη hcη hsη
  have HCa := exists_hilbertChartCodifferentialCommutatorLimit n k S χ η hχ hcχ hsχ hη hcη hsη
  let v := HRd.choose y + HCd.choose x
  let w := HRa.choose z + HCa.choose x
  have hv : Tendsto (fun j : ℕ => hilbertChartDifferential n (k+1) S χ η hχ hcχ hsχ hη hcη hsη
      ((j:ℝ)+1) (by positivity) x) atTop (𝓝 v) :=
    ((HRd.choose_spec.2 y).add (HCd.choose_spec.2 x)).congr (fun j =>
      (hilbertChartDifferential_weak n (k+1) S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) x y hy).symm)
  have hw : Tendsto (fun j : ℕ => hilbertChartCodifferential n k S χ η hχ hcχ hsχ hη hcη hsη
      ((j:ℝ)+1) (by positivity) x) atTop (𝓝 w) :=
    ((HRa.choose_spec.2 z).add (HCa.choose_spec.2 x)).congr (fun j =>
      (hilbertChartCodifferential_weak n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) x z hz).symm)
  exact ⟨v,w,jointGraphClosure_mem_of_limits n k
    (fun j : ℕ => hilbertChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) x)
    (fun j : ℕ => hilbertChartDifferential n (k+1) S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) x)
    (fun j : ℕ => hilbertChartCodifferential n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) x)
    (fun j => hilbertChartRegularizer_mem_jointGraphClosure n k S χ η hχ hcχ hsχ hη hcη hsη
      ((j:ℝ)+1) (by positivity) x) (L x) v w
    (hilbertChartRegularizer_tendsto_of_core n (k+1) S χ η hχ hcχ hsχ hη hcη hsη L hL x) hv hw⟩

end TernaryPoly.PolynomialFormCoordinates
