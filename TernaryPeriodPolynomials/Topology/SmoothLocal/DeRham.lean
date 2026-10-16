module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamRestriction
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldAtlas

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Actual smooth differential forms on an arithmetic quotient lifting chart form the de Rham complex. -/
def quotientChartComplex (S : Space) : CochainComplex (ModuleCat ℝ) ℕ :=
  complex (F := F) (quotientChart S).open_target

/-- Every point in an actual quotient chart has a ball on which every closed positive-degree
smooth coefficient-valued form has an actual smooth primitive. -/
theorem quotientChart_local_poincare (S : Space) {x : Coordinates}
    (hx : x ∈ (quotientChart S).target) :
    ∃ r > (0 : ℝ), ∃ hball : Metric.ball x r ⊆ (quotientChart S).target,
      ∀ (n : ℕ) (w : Form (F := F) (quotientChart S).target (n + 1)),
        d (quotientChart S).open_target (n + 1) w = 0 →
        ∃ z : Form (F := F) (Metric.ball x r) n,
          d Metric.isOpen_ball n z = restrictTo hball (n + 1) w :=
  local_poincare (quotientChart S).open_target hx

omit [FiniteDimensional ℝ F] in
/-- On each convex quotient-coordinate neighborhood, degree-zero closed forms are exactly
constant coefficient sections. -/
theorem quotientCoordinate_zero_kernel (x : Coordinates) (r : ℝ)
    (w : Form (F := F) (Metric.ball x r) 0) :
    d Metric.isOpen_ball 0 w = 0 ↔ ∃ c : F, w = constant (Metric.ball x r) c :=
  closed_zero_iff_constant Metric.isOpen_ball (convex_ball x r).isPreconnected w

end TernaryPoly.SmoothLocalDeRham
