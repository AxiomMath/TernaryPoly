module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Differential.CommutatorConvergence
public import TernaryPeriodPolynomials.DifferentialForm.Chart.CoordinateConvergence

@[expose] public section


/-! Actual Hilbert convergence of the literal compact differential chart commutators. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set Filter MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff Topology

theorem coreChartDifferentialCommutator_tendsto (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : Core n k) :
    Tendsto (fun j : ℕ => inclusion n (k+1)
      (coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη ((j:ℝ)+1) (by positivity) w))
      atTop (nhds (inclusion n (k+1) (coreChartDifferentialLimit n k S χ η hχ hη hcη hsη w))) := by
  let a (j : ℕ) := coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη
    ((j:ℝ)+1) (by positivity) w
  let b := coreChartDifferentialLimit n k S χ η hχ hη hcη hsη w
  let e (j : ℕ) : Core n (k+1) := a j - b
  have hs (j : ℕ) : quotientSupport (e j).val ⊆ (quotientChart S).symm '' tsupport η :=
    (quotientSupport_sub (a j).val b.val).trans (union_subset
      (quotientSupport_coreChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη
        ((j:ℝ)+1) (by positivity) w)
      (quotientSupport_coreChartDifferentialLimit n k S χ η hχ hη hcη hsη w))
  let f (j : ℕ) := components n (k+1)
    (globalChartRepresentative (deckRepresentation n) S (k+1) (e j).val).val
  have he (j : ℕ) (i : Index n (k+1)) : f j i = fun x =>
      components n (k+1) (globalChartRepresentative (deckRepresentation n) S (k+1) (a j).val).val i x -
      components n (k+1) (globalChartRepresentative (deckRepresentation n) S (k+1) b.val).val i x := by
    have hr := globalChartRepresentative_sub n (k+1) S (a j).val b.val
    apply (congrArg (fun p => components n (k+1) p i) hr).trans
    funext x
    exact congrArg (fun z : Index n (k+1) → ℝ => z i)
      ((coordinates n (k+1)).map_sub
        ((globalChartRepresentative (deckRepresentation n) S (k+1) (a j).val).val x)
        ((globalChartRepresentative (deckRepresentation n) S (k+1) b.val).val x))
  have ht (i : Index n (k+1)) : Tendsto (fun j : ℕ => ∫ x, ‖f j i x‖^2) atTop (nhds 0) :=
    (differentialCommutator_component_tendsto n k S χ η hχ hcχ hsχ hη hcη hsη w i).congr
      (fun j => (congrArg (fun p : Coordinates → ℝ => ∫ x, ‖p x‖^2) (he j i)).symm)
  have hz := chart_supported_inclusion_tendsto_zero n (k+1) S (tsupport η) hcη hsη e hs ht
  have hsum : Tendsto (fun j : ℕ => inclusion n (k+1) (e j) + inclusion n (k+1) b)
      atTop (nhds (inclusion n (k+1) b)) := by
    simpa only [zero_add] using hz.add_const (inclusion n (k+1) b)
  exact hsum.congr (fun j =>
    (congrArg (fun z : Hilbert n (k+1) => z + inclusion n (k+1) b)
      ((inclusion n (k+1)).map_sub (a j) b)).trans (sub_add_cancel _ _))

end TernaryPoly.PolynomialFormCoordinates
