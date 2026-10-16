module

public import TernaryPeriodPolynomials.DifferentialForm.JointGraph.Closure
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.GraphLimit
public import TernaryPeriodPolynomials.DifferentialForm.WeakTests

@[expose] public section


/-! Every simultaneous compact graph limit belongs to both genuine maximal weak graphs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open Set Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormCoordinates
open scoped ContDiff Topology

attribute [local instance] PolynomialFormConnection.cutoffHilbertModule
attribute [local irreducible] maximalDifferential maximalCodifferential

theorem jointGraphClosure_mem_maximal (n k : ℕ)
    {x : Hilbert n (k+1)} {y : Hilbert n ((k+1)+1)} {z : Hilbert n k}
    (h : (x,y,z) ∈ jointGraphClosure n k) :
    (x,y) ∈ (maximalDifferential n (k+1)).graph ∧ (x,z) ∈ (maximalCodifferential n k).graph := by
  have H := jointGraphClosure_exists_sequence n k h
  let u := H.choose
  have hd (a : Core n (k+1)) :
      (inclusion n (k+1) a, inclusion n ((k+1)+1)
        (compactDifferential (deckRepresentation n) isOpen_univ (k+1) a)) ∈
      (maximalDifferential n (k+1)).graph :=
    (mem_maximalDifferential_graph_iff n (k+1) _ _).mpr
      (inner_compactDifferential_compactAdjoint n (k+1) a)
  have ha (a : Core n (k+1)) :
      (inclusion n (k+1) a, inclusion n k (compactAdjoint n k a)) ∈ (maximalCodifferential n k).graph := by
    apply (mem_maximalCodifferential_graph_iff n k _ _).mpr
    intro b
    exact (real_inner_comm _ _).trans
      ((inner_compactDifferential_compactAdjoint n k b a).symm.trans (real_inner_comm _ _))
  exact ⟨(maximalDifferential_isClosed n (k+1)).mem_of_tendsto
    (H.choose_spec.1.prodMk_nhds H.choose_spec.2.1) (Eventually.of_forall (fun j => hd (u j))),
    (maximalCodifferential_isClosed n k).mem_of_tendsto
    (H.choose_spec.1.prodMk_nhds H.choose_spec.2.2) (Eventually.of_forall (fun j => ha (u j)))⟩

end TernaryPoly.PolynomialFormHilbert
