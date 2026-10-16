module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameSimplices

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Filter
open scoped Topology Simplicial

/-- Actual disjoint open-cover data on a topological space, with every point covered. -/
structure DisjointOpenCover (X : Type) [TopologicalSpace X] (ι : Type) where
  domain : ι → Set X
  isOpen_domain : ∀ i, IsOpen (domain i)
  disjoint : Pairwise (fun i j => Disjoint (domain i) (domain j))
  covers : ∀ x, ∃ i, x ∈ domain i

namespace DisjointOpenCover
variable {X ι : Type} [TopologicalSpace X] (U : DisjointOpenCover X ι)

/-- The unique actual open component label at a point. -/
def index (x : X) : ι := (U.covers x).choose

theorem index_mem (x : X) : x ∈ U.domain (U.index x) := (U.covers x).choose_spec

theorem index_eq_of_mem (i : ι) {x : X} (hx : x ∈ U.domain i) : U.index x = i := by
  by_contra h
  exact (U.disjoint h).le_bot ⟨U.index_mem x,hx⟩

/-- The actual component label is locally constant because the component opens are disjoint. -/
def label : LocallyConstant X ι :=
  ⟨U.index, (IsLocallyConstant.iff_eventually_eq _).mpr fun x => by
    filter_upwards [(U.isOpen_domain (U.index x)).mem_nhds (U.index_mem x)] with y hy
    exact U.index_eq_of_mem (U.index x) hy⟩

/-- The component label of a continuous map from a connected domain is constant. -/
theorem label_comp_eq {Y : Type} [TopologicalSpace Y] [PreconnectedSpace Y]
    (f : C(Y,X)) (a b : Y) : U.label (f a) = U.label (f b) :=
  (U.label.isLocallyConstant.comp_continuous f.continuous).apply_eq_of_isPreconnected
    isPreconnected_univ (mem_univ a) (mem_univ b)

end DisjointOpenCover
end TernaryPoly.SmoothSingularGlobal
