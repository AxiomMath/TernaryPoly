module

public import TernaryPeriodPolynomials.Analysis.Bounded.WeakCommutatorTransport
public import TernaryPeriodPolynomials.DifferentialForm.Chart.CommutatorHilbertIdentity
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.ChartTranspose
public import TernaryPeriodPolynomials.DifferentialForm.WeakTests

@[expose] public section


/-! The genuine weighted chart transpose transports actual maximal weak graph equations. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

variable (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (c : ℝ) (hc : 0 < c)

theorem hilbertChartDifferential_weak (x : Hilbert n k) (z : Hilbert n (k+1))
    (hx : (x,z) ∈ (maximalDifferential n k).graph) :
    hilbertChartDifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc x =
      hilbertChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc z +
      hilbertChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc x :=
  BoundedWeakCommutatorTransport.transport
    (inclusion n k) (inclusion n (k+1)) (inclusion_dense n k) (inclusion_dense n (k+1))
    (compactDifferential (deckRepresentation n) isOpen_univ k) (compactAdjoint n k)
    (fun b : Core n (k+1) => chartTranspose n (k+1) S χ η c hc.ne' hχ hcχ hsχ hη hsη b.val)
    (hilbertChartRegularizer n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartDifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartDifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (inner_compactDifferential_compactAdjoint n k)
    (inner_hilbertChartRegularizer_transpose n (k+1) S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartDifferential_sub_commutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc) x z
    ((mem_maximalDifferential_graph_iff n k x z).mp hx)

theorem hilbertChartCodifferential_weak (x : Hilbert n (k+1)) (z : Hilbert n k)
    (hx : (x,z) ∈ (maximalCodifferential n k).graph) :
    hilbertChartCodifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc x =
      hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc z +
      hilbertChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc x := by
  have hpair (a : Core n (k+1)) (b : Core n k) :
      inner ℝ (inclusion n k (compactAdjoint n k a)) (inclusion n k b) =
      inner ℝ (inclusion n (k+1) a)
        (inclusion n (k+1) (compactDifferential (deckRepresentation n) isOpen_univ k b)) :=
    (real_inner_comm _ _).trans
      ((inner_compactDifferential_compactAdjoint n k b a).symm.trans (real_inner_comm _ _))
  exact BoundedWeakCommutatorTransport.transport
    (inclusion n (k+1)) (inclusion n k) (inclusion_dense n (k+1)) (inclusion_dense n k)
    (compactAdjoint n k) (compactDifferential (deckRepresentation n) isOpen_univ k)
    (fun b : Core n k => chartTranspose n k S χ η c hc.ne' hχ hcχ hsχ hη hsη b.val)
    (hilbertChartRegularizer n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartCodifferential n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartCodifferentialCommutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    hpair (inner_hilbertChartRegularizer_transpose n k S χ η hχ hcχ hsχ hη hcη hsη c hc)
    (hilbertChartCodifferential_sub_commutator n k S χ η hχ hcχ hsχ hη hcη hsη c hc) x z
    ((mem_maximalCodifferential_graph_iff n k x z).mp hx)

end TernaryPoly.PolynomialFormCoordinates
