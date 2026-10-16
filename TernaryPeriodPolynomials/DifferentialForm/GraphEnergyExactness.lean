module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.GraphEnergyExactness
public import TernaryPeriodPolynomials.DifferentialForm.JointGraph.Energy
public import TernaryPeriodPolynomials.DifferentialForm.MinimalAdjoints
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.GraphLimit

@[expose] public section


/-! Actual analytic exactness reduces only to the genuine simultaneous graph approximation. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open Set PolynomialFormCoordinates PolynomialCoefficientMetric SmoothCoveringDeRham
open scoped LinearPMap
attribute [local instance] PolynomialFormConnection.cutoffHilbertModule
attribute [local irreducible] minimalDifferential maximalDifferential maximalCodifferential

theorem minimal_maximal_differential_complex (n k : ℕ) (a : (minimalDifferential n k).domain) :
    minimalDifferential n k a ∈ HilbertClosedOperator.kernel (maximalDifferential n (k+1)) :=
  LinearPMap.le_graph_of_le (minimalDifferential_le_maximal n (k+1))
    (minimalDifferential_complex n k a)

theorem exact_of_jointGraphClosure {n : ℕ} (hn : 0 < n)
    (hJ : ∀ (x : Hilbert n 2) (y : Hilbert n 3) (z : Hilbert n 1),
      (x,y) ∈ (maximalDifferential n 2).graph → (x,z) ∈ (maximalCodifferential n 1).graph →
      (x,y,z) ∈ jointGraphClosure n 1) :
    (HilbertClosedOperator.kernel (maximalDifferential n 2) : Set (Hilbert n 2)) =
      Set.range (minimalDifferential n 1) := by
  have H := jointGraphClosure_energy_coercive hn
  exact HilbertClosedOperator.exact_of_graph_energy (minimalDifferential n 1) (maximalDifferential n 2)
    (maximalCodifferential n 1) (minimalDifferential_isClosed n 1) (minimalDifferential_domain_dense n 1)
    (maximalDifferential_isClosed n 2) (minimal_maximal_differential_complex n 1)
    (minimalDifferential_adjoint n 1) H.choose H.choose_spec.1
    (fun x y z hy hz => H.choose_spec.2 x y z (hJ x y z hy hz))

end TernaryPoly.PolynomialFormHilbert
