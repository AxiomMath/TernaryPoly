module

public import TernaryPeriodPolynomials.Analysis.JointEmbeddedGraphClosure
public import TernaryPeriodPolynomials.DifferentialForm.Chart.SimultaneousApproximation

@[expose] public section


/-! The actual closed submodule of simultaneous compact value/differential/adjoint triples. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open Set Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormCoordinates
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff Topology

def jointGraphClosure (n k : ℕ) :
    Submodule ℝ (Hilbert n (k+1) × Hilbert n (k+2) × Hilbert n k) :=
  JointEmbeddedGraphClosure.graph (inclusion n (k+1))
    ((inclusion n (k+2)).comp (compactDifferential (deckRepresentation n) isOpen_univ (k+1)))
    ((inclusion n k).comp (compactAdjoint n k))

theorem jointGraphClosure_exists_sequence (n k : ℕ)
    {x : Hilbert n (k+1)} {y : Hilbert n (k+2)} {z : Hilbert n k}
    (h : (x,y,z) ∈ jointGraphClosure n k) :
    ∃ u : ℕ → Core n (k+1),
      Tendsto (fun j => inclusion n (k+1) (u j)) atTop (𝓝 x) ∧
      Tendsto (fun j => inclusion n (k+2)
        (compactDifferential (deckRepresentation n) isOpen_univ (k+1) (u j))) atTop (𝓝 y) ∧
      Tendsto (fun j => inclusion n k (compactAdjoint n k (u j))) atTop (𝓝 z) :=
  JointEmbeddedGraphClosure.exists_sequence _ _ _ h

theorem jointGraphClosure_mem_of_limits (n k : ℕ)
    (u : ℕ → Hilbert n (k+1)) (v : ℕ → Hilbert n (k+2)) (w : ℕ → Hilbert n k)
    (h : ∀ j, (u j,v j,w j) ∈ jointGraphClosure n k)
    (x : Hilbert n (k+1)) (y : Hilbert n (k+2)) (z : Hilbert n k)
    (hx : Tendsto u atTop (𝓝 x)) (hy : Tendsto v atTop (𝓝 y)) (hz : Tendsto w atTop (𝓝 z)) :
    (x,y,z) ∈ jointGraphClosure n k :=
  JointEmbeddedGraphClosure.mem_of_limits _ _ _ u v w h x y z hx hy hz

theorem hilbertChartRegularizer_mem_jointGraphClosure (n k : ℕ) (S : Space)
    (χ η : Coordinates → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : 0 < c) (x : Hilbert n (k+1)) :
    (hilbertChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc x,
      hilbertChartDifferential n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc x,
      hilbertChartCodifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc x) ∈ jointGraphClosure n k := by
  have H := hilbertChartRegularizer_simultaneous_approximation n k S χ η hχ hcχ hsχ hη hcη hsη c hc x
  exact JointEmbeddedGraphClosure.mem_of_sequence _ _ _ H.choose _ _ _
    H.choose_spec.1 H.choose_spec.2.1 H.choose_spec.2.2

end TernaryPoly.PolynomialFormHilbert
