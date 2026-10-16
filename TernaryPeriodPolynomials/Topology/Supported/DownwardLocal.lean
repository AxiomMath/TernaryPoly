module

public import TernaryPeriodPolynomials.Topology.Supported.DownwardModel
public import TernaryPeriodPolynomials.Topology.Supported.InwardExtension
public import TernaryPeriodPolynomials.SymmetricSpace.BoundaryNeighborhood.Homotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.SupportedDownward
open scoped unitInterval
open Metric SupportedInward
variable {E X : Type*} [MetricSpace E] [TopologicalSpace X]

/-- Choose a supporting ball entirely inside the chart and a prescribed open neighborhood. -/
theorem exists_chart_radius (W : Set X) (hW : IsOpen W)
    (e : OpenPartialHomeomorph X (Model E)) (x : X) (hx : x ∈ e.source) (hxW : x ∈ W) :
    ∃ r : ℝ, 0 < r ∧ closedBall (e x) (2 * r) ⊆ e.target ∩ e.symm ⁻¹' W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (e.isOpen_inter_preimage_symm hW)
    (e x) ⟨e.map_source hx, by simpa only [Set.mem_preimage, e.left_inv hx] using hxW⟩
  refine ⟨ε / 3, by positivity, ?_⟩
  exact (closedBall_subset_ball (by linarith : 2 * (ε / 3) < ε)).trans hball

variable [ProperSpace E] [T2Space X]

/-- A compactly supported boundary-fixing chart deformation preserving the prescribed W. -/
def localDeformation (A W : Set X) (e : OpenPartialHomeomorph X (Model E))
    (hA : ∀ x ∈ e.source, x ∈ A ↔ (e x).2.val = 0)
    (z : Model E) (hz : z.2.val = 0) (r : ℝ) (hr : 0 < r)
    (hball : closedBall z (2 * r) ⊆ e.target ∩ e.symm ⁻¹' W) :
    BoundaryNeighborhood.Deformation A W where
  homotopy := ⟨chartPush e (fun p => down z r p.1 p.2),
    chartPush_continuous e _ (down_continuous z r)
      (down_mem z hz r hr e.target (fun y hy => (hball hy).1))
      (closedBall z (2 * r)) (isCompact_closedBall z (2 * r))
      (fun y hy => (hball hy).1)
      (fun t y hy => down_eq z r t y (cutoff_zero z r hr y
        (le_of_lt (not_le.mp (by simpa only [mem_closedBall] using hy)))))⟩
  zero x := by
    change chartPush e (fun p => down z r p.1 p.2) (0, x) = x
    by_cases hx : x ∈ e.source
    · rw [chartPush_source e _ 0 x hx, down_zero, e.left_inv hx]
    · exact chartPush_outside e _ 0 x hx
  fixes t x hx := by
    change chartPush e (fun p => down z r p.1 p.2) (t, x) = x
    by_cases hs : x ∈ e.source
    · rw [chartPush_source e _ t x hs, down_boundary z r t (e x) ((hA x hs).mp hx),
        e.left_inv hs]
    · exact chartPush_outside e _ t x hs
  preserves t x hx := by
    change chartPush e (fun p => down z r p.1 p.2) (t, x) ∈ W
    by_cases hs : x ∈ e.source
    · rw [chartPush_source e _ t x hs]
      exact (down_mem z hz r hr (e.target ∩ e.symm ⁻¹' W) hball t (e x)
        ⟨e.map_source hs, by simpa only [Set.mem_preimage, e.left_inv hs] using hx⟩).2
    · rwa [chartPush_outside e _ t x hs]

/-- The entire radius-r chart core collapses to the boundary at time one. -/
theorem localDeformation_core (A W : Set X) (e : OpenPartialHomeomorph X (Model E))
    (hA : ∀ x ∈ e.source, x ∈ A ↔ (e x).2.val = 0)
    (z : Model E) (hz : z.2.val = 0) (r : ℝ) (hr : 0 < r)
    (hball : closedBall z (2 * r) ⊆ e.target ∩ e.symm ⁻¹' W)
    (y : X) (hy : y ∈ e.source ∩ e ⁻¹' ball z r) :
    (localDeformation A W e hA z hz r hr hball).homotopy (1, y) ∈ A := by
  change chartPush e (fun p => down z r p.1 p.2) (1, y) ∈ A
  rw [chartPush_source e _ 1 y hy.1]
  have ht := down_mem z hz r hr e.target (fun v hv => (hball hv).1) 1 (e y)
    (e.map_source hy.1)
  apply (hA _ (e.map_target ht)).mpr
  rw [e.right_inv ht]
  exact down_one_height z r hr (e y) (le_of_lt hy.2)

/-- Every boundary point in a genuine half-space chart has a local supported collapse. -/
theorem exists_localDeformation (A W : Set X) (hW : IsOpen W) (hAW : A ⊆ W)
    (e : OpenPartialHomeomorph X (Model E))
    (hA : ∀ x ∈ e.source, x ∈ A ↔ (e x).2.val = 0)
    (x : X) (hx : x ∈ e.source) (hxA : x ∈ A) :
    ∃ d : BoundaryNeighborhood.Deformation A W, ∃ V : Set X,
      IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, d.homotopy (1, y) ∈ A := by
  obtain ⟨r, hr, hball⟩ := exists_chart_radius W hW e x hx (hAW hxA)
  have hz := (hA x hx).mp hxA
  refine ⟨localDeformation A W e hA (e x) hz r hr hball,
    e.source ∩ e ⁻¹' ball (e x) r, e.isOpen_inter_preimage isOpen_ball, ?_, ?_⟩
  · exact ⟨hx, by simpa only [Set.mem_preimage, mem_ball, dist_self] using hr⟩
  · exact localDeformation_core A W e hA (e x) hz r hr hball

end TernaryPoly.SupportedDownward
