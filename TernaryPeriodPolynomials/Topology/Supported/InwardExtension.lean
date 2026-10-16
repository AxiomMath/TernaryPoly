module

public import TernaryPeriodPolynomials.Topology.InwardHomotopyBasic
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Topology.Compactness.Compact

@[expose] public section


noncomputable section
namespace TernaryPoly.SupportedInward
open scoped unitInterval
open Topology Filter
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Extend a chart deformation by the identity away from the chart source. -/
def chartPush (e : OpenPartialHomeomorph X Y) (F : I × Y → Y) (p : I × X) : X := by
  classical
  exact if p.2∈e.source then e.symm (F (p.1,e p.2)) else p.2

theorem chartPush_source (e : OpenPartialHomeomorph X Y) (F : I × Y → Y)
    (t : I) (x : X) (hx : x∈e.source) :
    chartPush e F (t,x)=e.symm (F (t,e x)) := by
  classical
  simp [chartPush,hx]

theorem chartPush_outside (e : OpenPartialHomeomorph X Y) (F : I × Y → Y)
    (t : I) (x : X) (hx : x∉e.source) : chartPush e F (t,x)=x := by
  classical
  simp [chartPush,hx]

/-- The extended deformation is the identity off the chart image of its support. -/
theorem chartPush_off_support (e : OpenPartialHomeomorph X Y) (F : I × Y → Y)
    (K : Set Y) (hF : ∀ t y,y∉K → F (t,y)=y)
    (t : I) (x : X) (hx : x∉e.symm '' K) : chartPush e F (t,x)=x := by
  by_cases hs : x∈e.source
  · rw [chartPush_source e F t x hs,hF t (e x) (by
      intro he
      exact hx ⟨e x,he,e.left_inv hs⟩),e.left_inv hs]
  · exact chartPush_outside e F t x hs

/-- A compactly supported chart deformation extends continuously across the source boundary. -/
theorem chartPush_continuous [T2Space X]
    (e : OpenPartialHomeomorph X Y) (F : I × Y → Y) (hF : Continuous F)
    (hV : ∀ t y,y∈e.target → F (t,y)∈e.target)
    (K : Set Y) (hK : IsCompact K) (hKV : K⊆e.target)
    (hfix : ∀ t y,y∉K → F (t,y)=y) : Continuous (chartPush e F) := by
  have hclosed : IsClosed (e.symm '' K) :=
    (hK.image_of_continuousOn (e.symm.continuousOn.mono hKV)).isClosed
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.2∈e.source
  · have hpair : ContinuousAt (fun q : I × X => (q.1,e q.2)) p :=
      continuous_fst.continuousAt.prodMk ((e.continuousAt hp).comp continuous_snd.continuousAt)
    have hmiddle : ContinuousAt (fun q : I × X => F (q.1,e q.2)) p := hF.continuousAt.comp hpair
    have hcomp : ContinuousAt (fun q : I × X => e.symm (F (q.1,e q.2))) p := (e.continuousAt_symm (hV p.1 (e p.2) (e.map_source hp))).comp
      (f := fun q : I × X => F (q.1,e q.2)) hmiddle
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hp)] with q hq
    exact chartPush_source e F q.1 q.2 hq
  · have hout : p.2∉e.symm '' K := by
      rintro ⟨y,hy,he⟩
      exact hp (he ▸ e.map_target (hKV hy))
    apply continuous_snd.continuousAt.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hout)] with q hq
    exact chartPush_off_support e F K hfix q.1 q.2 hq

end TernaryPoly.SupportedInward
