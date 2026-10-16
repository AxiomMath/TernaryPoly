module

public import TernaryPeriodPolynomials.Topology.Supported.InwardLocal

@[expose] public section


noncomputable section
namespace TernaryPoly.SupportedInward
open scoped unitInterval
open Metric
variable {E X : Type*} [MetricSpace E] [ProperSpace E] [TopologicalSpace X] [T2Space X]

/-- The local deformation has compact spatial support strictly inside its chart source. -/
theorem localDeformation_support (U : Set X) (e : OpenPartialHomeomorph X (Model E))
    (hU : ∀ x∈e.source,x∈U ↔ 0<(e x).2.val)
    (z : Model E) (r : ℝ) (hr : 0<r) (hball : closedBall z (2*r)⊆e.target) :
    IsCompact (e.symm '' closedBall z r) ∧ e.symm '' closedBall z r⊆e.source ∧
    ∀ t x,x∉e.symm '' closedBall z r →
      (localDeformation U e hU z r hr hball).homotopy (t,x)=x := by
  have hK : closedBall z r⊆e.target :=
    (closedBall_subset_closedBall (by linarith : r≤2*r)).trans hball
  refine ⟨(isCompact_closedBall z r).image_of_continuousOn
    (e.symm.continuousOn.mono hK),?_,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    exact e.map_target (hK hy)
  · intro t x hx
    change chartPush e (fun p => push z r p.1 p.2) (t,x)=x
    apply chartPush_off_support e _ (closedBall z r) _ t x hx
    intro s y hy
    exact push_eq z r s y (bump_zero z r y
      (le_of_lt (not_le.mp (by simpa only [mem_closedBall] using hy))))

/-- An atlas with the literal positive-height interior criterion supplies inward deformations
at every point, using only ordinary topological half-space charts. -/
theorem pointwise_localDeformation (U : Set X)
    (hatlas : ∀ x : X,∃ e : OpenPartialHomeomorph X (Model E),x∈e.source ∧
      ∀ y∈e.source,y∈U ↔ 0<(e y).2.val) :
    ∀ x : X,∃ H : InwardHomotopy.LocalDeformation U,H.homotopy (1,x)∈U := by
  intro x
  obtain ⟨e,hx,hU⟩ := hatlas x
  exact exists_localDeformation U e hU x hx

end TernaryPoly.SupportedInward
