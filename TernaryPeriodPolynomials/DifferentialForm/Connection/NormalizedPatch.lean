module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.NormalizedRadius
public import TernaryPeriodPolynomials.DifferentialForm.Connection.ScalarDifferentialBound
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.ShrinkingLemma

@[expose] public section


/-! Relatively compact normalized coordinate patches for finite quantitative smoothing. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set Metric
open scoped ContDiff Manifold Bundle Topology
attribute [local instance] orbitMetricSpace

/-- Pull back a convex coordinate ball inside a normalized chart. -/
def normalizedPatch (q : OrbitSpace) (r : ℝ) : Set OrbitSpace :=
  (normalizedChart q).source ∩ normalizedChart q ⁻¹' ball (normalizedChart q q) r

theorem isOpen_normalizedPatch (q : OrbitSpace) (r : ℝ) : IsOpen (normalizedPatch q r) :=
  (normalizedChart q).isOpen_inter_preimage isOpen_ball

theorem mem_normalizedPatch (q : OrbitSpace) {r : ℝ} (hr : 0 < r) : q ∈ normalizedPatch q r := by
  refine ⟨?_, mem_ball_self hr⟩
  rw [normalizedChart_source]
  exact mem_chart_source Coordinates q

theorem normalizedPatch_subset_source (q : OrbitSpace) (r : ℝ) :
    normalizedPatch q r ⊆ (normalizedChart q).source := inter_subset_left

/-- Compactness is proved by the actual inverse image of a compact coordinate ball. -/
theorem isCompact_closure_normalizedPatch (q : OrbitSpace) (r : ℝ)
    (h : closedBall (normalizedChart q q) r ⊆ (normalizedChart q).target) :
    IsCompact (closure (normalizedPatch q r)) := by
  have hc := isCompact_normalizedChart_symm_closedBall q r h
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro y hy
  refine ⟨normalizedChart q y, ball_subset_closedBall hy.2, ?_⟩
  exact (normalizedChart q).left_inv hy.1

/-- The derivative bound on a normalized closed ball controls the chart on its patch. -/
theorem norm_normalizedChartDerivative_le_on_patch (q : OrbitSpace) (r : ℝ)
    (h : ∀ v ∈ ball (normalizedChart q q) r,
      ‖normalizedChartDerivative q ((normalizedChart q).symm v)‖ ≤ 2) :
    ∀ y ∈ normalizedPatch q r, ‖normalizedChartDerivative q y‖ ≤ 2 := by
  intro y hy
  have he := congrArg (fun z : OrbitSpace => ‖normalizedChartDerivative q z‖)
    ((normalizedChart q).left_inv hy.1)
  exact he ▸ h (normalizedChart q y) hy.2

/-- A subordinate smooth scalar has compact support and a bound in the true dual metric. -/
theorem scalar_bounds_of_normalizedPatch (q : OrbitSpace) (r : ℝ)
    (h : ∀ v ∈ closedBall (normalizedChart q q) r,
      v ∈ (normalizedChart q).target ∧
        ‖normalizedChartDerivative q ((normalizedChart q).symm v)‖ ≤ 2)
    (φ : OrbitSpace → ℝ) (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ φ)
    (hs : tsupport φ ⊆ normalizedPatch q r) :
    HasCompactSupport φ ∧ ∃ D > 0, ∀ y, ‖scalarDifferential φ y‖ ≤ D := by
  have hc := isCompact_closure_normalizedPatch q r (fun v hv => (h v hv).1)
  have hK : HasCompactSupport φ := hc.of_isClosed_subset (isClosed_tsupport φ)
    (hs.trans subset_closure)
  refine ⟨hK, exists_scalarDifferential_bound q φ hφ hK
    (hs.trans (normalizedPatch_subset_source q r)) ?_⟩
  exact fun y hy => norm_normalizedChartDerivative_le_on_patch q r
    (fun v hv => (h v (ball_subset_closedBall hv)).2) y (hs hy)

end TernaryPoly.SymmetricSpaceRiemannian
