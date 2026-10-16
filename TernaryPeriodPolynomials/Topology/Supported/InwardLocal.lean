module

public import TernaryPeriodPolynomials.Topology.Supported.InwardModel
public import TernaryPeriodPolynomials.Topology.Supported.InwardExtension

@[expose] public section


noncomputable section
namespace TernaryPoly.SupportedInward
open scoped unitInterval
open Metric
variable {E X : Type*} [MetricSpace E] [TopologicalSpace X]

/-- Choose a supported chart ball together with room for every vertical displacement. -/
theorem exists_chart_radius (e : OpenPartialHomeomorph X (Model E)) (x : X)
    (hx : x∈e.source) : ∃ r : ℝ,0<r ∧ closedBall (e x) (2*r)⊆e.target := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  refine ⟨ε/3,by positivity,?_⟩
  exact (closedBall_subset_ball (by linarith : 2*(ε/3)<ε)).trans hball

variable [ProperSpace E] [T2Space X]

/-- A supported vertical chart push as an ordinary local interior-preserving deformation. -/
def localDeformation (U : Set X) (e : OpenPartialHomeomorph X (Model E))
    (hU : ∀ x∈e.source,x∈U ↔ 0<(e x).2.val)
    (z : Model E) (r : ℝ) (hr : 0<r) (hball : closedBall z (2*r)⊆e.target) :
    InwardHomotopy.LocalDeformation U where
  homotopy := ⟨chartPush e (fun p => push z r p.1 p.2),
    chartPush_continuous e _ (push_continuous z r)
      (push_mem z r hr e.target hball) (closedBall z r) (isCompact_closedBall z r)
      ((closedBall_subset_closedBall (by linarith : r≤2*r)).trans hball)
      (fun t y hy => push_eq z r t y (bump_zero z r y (le_of_lt (not_le.mp (by simpa only [mem_closedBall] using hy)))))⟩
  zero x := by
    change chartPush e (fun p => push z r p.1 p.2) (0,x)=x
    by_cases hx : x∈e.source
    · rw [chartPush_source e _ 0 x hx,push_zero,e.left_inv hx]
    · exact chartPush_outside e _ 0 x hx
  preserves t x hx := by
    change chartPush e (fun p => push z r p.1 p.2) (t,x)∈U
    by_cases hs : x∈e.source
    · rw [chartPush_source e _ t x hs]
      have ht := push_mem z r hr e.target hball t (e x) (e.map_source hs)
      apply (hU _ (e.map_target ht)).mpr
      rw [e.right_inv ht]
      exact ((hU x hs).mp hx).trans_le (push_height_mono z r t (e x))
    · rwa [chartPush_outside e _ t x hs]
  endpoint_fixed x hx := by
    change chartPush e (fun p => push z r p.1 p.2) (1,x)∉U at hx
    change chartPush e (fun p => push z r p.1 p.2) (1,x)=x
    by_cases hs : x∈e.source
    · rw [chartPush_source e _ 1 x hs] at hx ⊢
      have ht := push_mem z r hr e.target hball 1 (e x) (e.map_source hs)
      have hn : ¬0<(push z r 1 (e x)).2.val := by
        intro hp
        apply hx
        apply (hU _ (e.map_target ht)).mpr
        rwa [e.right_inv ht]
      rw [push_endpoint_fixed z r (e x) hn,e.left_inv hs]
    · exact chartPush_outside e _ 1 x hs

/-- The center of a supported chart push is interior at time one. -/
theorem localDeformation_center (U : Set X) (e : OpenPartialHomeomorph X (Model E))
    (hU : ∀ x∈e.source,x∈U ↔ 0<(e x).2.val)
    (x : X) (hx : x∈e.source) (r : ℝ) (hr : 0<r)
    (hball : closedBall (e x) (2*r)⊆e.target) :
    (localDeformation U e hU (e x) r hr hball).homotopy (1,x)∈U := by
  change chartPush e (fun p => push (e x) r p.1 p.2) (1,x)∈U
  rw [chartPush_source e _ 1 x hx]
  have ht := push_mem (e x) r hr e.target hball 1 (e x) (e.map_source hx)
  apply (hU _ (e.map_target ht)).mpr
  rw [e.right_inv ht]
  exact push_center_positive (e x) r hr

/-- Every point in an actual half-space chart has a supported local inward deformation. -/
theorem exists_localDeformation (U : Set X) (e : OpenPartialHomeomorph X (Model E))
    (hU : ∀ x∈e.source,x∈U ↔ 0<(e x).2.val)
    (x : X) (hx : x∈e.source) :
    ∃ H : InwardHomotopy.LocalDeformation U,H.homotopy (1,x)∈U := by
  obtain ⟨r,hr,hball⟩ := exists_chart_radius e x hx
  exact ⟨localDeformation U e hU (e x) r hr hball,
    localDeformation_center U e hU x hx r hr hball⟩

end TernaryPoly.SupportedInward
