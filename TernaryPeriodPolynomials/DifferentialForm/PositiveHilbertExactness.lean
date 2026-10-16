module

public import TernaryPeriodPolynomials.DifferentialForm.GraphEnergyExactness
public import TernaryPeriodPolynomials.DifferentialForm.JointGraph.Density

@[expose] public section


/-! Unconditional actual Hilbert exactness in degree two for every positive polynomial degree. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open Set PolynomialFormCoordinates PolynomialCoefficientMetric SmoothCoveringDeRham
attribute [local instance] PolynomialFormConnection.cutoffHilbertModule
attribute [local irreducible] minimalDifferential maximalDifferential maximalCodifferential

theorem positive_degree_hilbert_exact {n : ℕ} (hn : 0 < n) :
    (HilbertClosedOperator.kernel (maximalDifferential n 2) : Set (Hilbert n 2)) =
      Set.range (minimalDifferential n 1) :=
  exact_of_jointGraphClosure hn (maximal_triple_mem_jointGraphClosure n 1)

theorem closed_compact_has_weak_primitive {n : ℕ} (hn : 0 < n) (ω : Core n 2)
    (hω : compactDifferential (deckRepresentation n) isOpen_univ 2 ω = 0) :
    ∃ u : Hilbert n 1, (u,inclusion n 2 ω) ∈ (maximalDifferential n 1).graph := by
  have hzero : inclusion n 3 (compactDifferential (deckRepresentation n) isOpen_univ 2 ω) = 0 :=
    (congrArg (inclusion n 3) hω).trans (map_zero _)
  have hmem : inclusion n 2 ω ∈ HilbertClosedOperator.kernel (maximalDifferential n 2) := by
    apply (mem_maximalDifferential_graph_iff n 2 (inclusion n 2 ω) 0).mpr
    intro b
    exact (congrArg (fun y : Hilbert n 3 => inner ℝ y (inclusion n 3 b)) hzero).symm.trans
      (inner_compactDifferential_compactAdjoint n 2 ω b)
  have hr : inclusion n 2 ω ∈ Set.range (minimalDifferential n 1) :=
    (congrArg (fun s : Set (Hilbert n 2) => inclusion n 2 ω ∈ s) (positive_degree_hilbert_exact hn)).mp hmem
  obtain ⟨a,ha⟩ := hr
  have hg := LinearPMap.le_graph_of_le (minimalDifferential_le_maximal n 1)
    ((minimalDifferential n 1).mem_graph a)
  exact ⟨a,(congrArg (fun y : Hilbert n 2 => ((a : Hilbert n 1),y) ∈ (maximalDifferential n 1).graph) ha).mp hg⟩

end TernaryPoly.PolynomialFormHilbert
