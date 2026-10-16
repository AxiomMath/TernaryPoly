module

public import TernaryPeriodPolynomials.DifferentialForm.JointGraph.Closure
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Cancellation

@[expose] public section


/-! Actual positive-degree compact coercivity persists on the simultaneous graph closure. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open Filter PolynomialFormCoordinates PolynomialCoefficientMetric SmoothCoveringDeRham
open scoped Topology

theorem jointGraphClosure_energy_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : Hilbert n 2) (y : Hilbert n 3) (z : Hilbert n 1),
      (x,y,z) ∈ jointGraphClosure n 1 → c * ‖x‖^2 ≤ ‖z‖^2 + ‖y‖^2 := by
  have H := PolynomialFormGeometricEnergy.norm_differential_energy_coercive hn
  let c : ℝ := H.choose
  refine ⟨c,H.choose_spec.1,fun x y z h => ?_⟩
  have A := jointGraphClosure_exists_sequence n 1 h
  have hi := A.choose_spec.1
  have hd := A.choose_spec.2.1
  have ha := A.choose_spec.2.2
  exact le_of_tendsto_of_tendsto (hi.norm.pow 2 |>.const_mul c)
    ((ha.norm.pow 2).add (hd.norm.pow 2))
    (Filter.Eventually.of_forall (fun j => H.choose_spec.2 (A.choose j)))

end TernaryPoly.PolynomialFormHilbert
