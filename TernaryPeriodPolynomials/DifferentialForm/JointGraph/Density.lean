module

public import TernaryPeriodPolynomials.DifferentialForm.Compact.JointGraph
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff

@[expose] public section

/-! Genuine global simultaneous smooth compact approximation for the actual maximal form graphs. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open Set Filter PolynomialFormCoordinates PolynomialFormConnection PolynomialCoefficientMetric SmoothCoveringDeRham
open scoped Topology
attribute [local instance] cutoffHilbertModule
attribute [local irreducible] maximalDifferential maximalCodifferential

theorem maximal_triple_mem_jointGraphClosure (n k : ℕ)
    (x : Hilbert n (k+1)) (y : Hilbert n ((k+1)+1)) (z : Hilbert n k)
    (hy : (x,y) ∈ (maximalDifferential n (k+1)).graph)
    (hz : (x,z) ∈ (maximalCodifferential n k).graph) :
    (x,y,z) ∈ jointGraphClosure n k := by
  have H := exists_simultaneous_compact_weak_graph_approximation n k x y z hy hz
  let u := H.choose
  let v := H.choose_spec.choose
  let w := H.choose_spec.choose_spec.choose
  have A := H.choose_spec.choose_spec.choose_spec
  have h (j : ℕ) : (u j,v j,w j) ∈ jointGraphClosure n k := by
    have B := A.2.2.1 j
    exact compact_weak_triple_mem_jointGraphClosure n k B.choose B.choose_spec.1 (u j) (v j) (w j)
      B.choose_spec.2.1 (A.1 j) (A.2.1 j)
  exact jointGraphClosure_mem_of_limits n k u v w h x y z A.2.2.2.1 A.2.2.2.2.1 A.2.2.2.2.2

theorem exists_simultaneous_compact_graph_approximation (n k : ℕ)
    (x : Hilbert n (k+1)) (y : Hilbert n ((k+1)+1)) (z : Hilbert n k)
    (hy : (x,y) ∈ (maximalDifferential n (k+1)).graph)
    (hz : (x,z) ∈ (maximalCodifferential n k).graph) :
    ∃ u : ℕ → Core n (k+1),
      Tendsto (fun j => inclusion n (k+1) (u j)) atTop (𝓝 x) ∧
      Tendsto (fun j => inclusion n ((k+1)+1)
        (compactDifferential (deckRepresentation n) isOpen_univ (k+1) (u j))) atTop (𝓝 y) ∧
      Tendsto (fun j => inclusion n k (compactAdjoint n k (u j))) atTop (𝓝 z) :=
  jointGraphClosure_exists_sequence n k (maximal_triple_mem_jointGraphClosure n k x y z hy hz)

end TernaryPoly.PolynomialFormHilbert
