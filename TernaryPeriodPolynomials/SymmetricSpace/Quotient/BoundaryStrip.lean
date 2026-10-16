module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ChartsProduct
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientBoundary
open Topology SymmetricSpaceBoundaryCharts

/-- The zero-height point of the closed half-line. -/
def heightZero : HalfLine := ⟨0,le_rfl⟩

def radiusSet (ε : ℝ) : Set HalfLine := {r | r.val<ε}
abbrev Radius (ε : ℝ) := {r : HalfLine // r.val<ε}

theorem radiusSet_isOpen (ε : ℝ) : IsOpen (radiusSet ε) :=
  isOpen_lt continuous_subtype_val continuous_const

/-- Every open half-line neighborhood of zero contains a genuine initial interval [0,ε). -/
theorem exists_radius_subset {V : Set HalfLine} (hV : IsOpen V) (h0 : heightZero∈V) :
    ∃ ε : ℝ, 0<ε ∧ radiusSet ε⊆V := by
  obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp hV heightZero h0
  refine ⟨ε,hε,?_⟩
  intro r hr
  change r.val<ε at hr
  apply hεV
  change dist r.val 0<ε
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg r.property] using hr

/-- An open product half-space neighborhood of a boundary point contains a product collar strip. -/
theorem exists_open_strip {W : Set ProductModel} (hW : IsOpen W)
    (v : BoundaryCoordinates) (hv : (v,heightZero)∈W) :
    ∃ U : Set BoundaryCoordinates, IsOpen U ∧ v∈U ∧
      ∃ ε : ℝ, 0<ε ∧ U ×ˢ radiusSet ε⊆W := by
  obtain ⟨U,V,hU,hV,hvU,h0V,hUV⟩ := isOpen_prod_iff.mp hW v heightZero hv
  obtain ⟨ε,hε,hεV⟩ := exists_radius_subset hV h0V
  exact ⟨U,hU,hvU,ε,hε,Set.prod_mono (Set.Subset.refl _) hεV |>.trans hUV⟩

/-- The literal inclusion of U×[0,ε) into the product half-space. -/
def stripInclusion (U : Set BoundaryCoordinates) (ε : ℝ) : U × Radius ε → ProductModel :=
  fun p => (p.1.val,p.2.val)

theorem stripInclusion_isOpenEmbedding {U : Set BoundaryCoordinates} (hU : IsOpen U) (ε : ℝ) :
    IsOpenEmbedding (stripInclusion U ε) :=
  hU.isOpenEmbedding_subtypeVal.prodMap (radiusSet_isOpen ε).isOpenEmbedding_subtypeVal

@[simp] theorem stripInclusion_range (U : Set BoundaryCoordinates) (ε : ℝ) :
    Set.range (stripInclusion U ε)=U ×ˢ radiusSet ε := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨q.1.property,q.2.property⟩
  · rintro ⟨hU,hε⟩
    exact ⟨(⟨p.1,hU⟩,⟨p.2,hε⟩),rfl⟩

/-- An open embedding whose image lies in a partial chart remains an open embedding after
composition with that chart. -/
theorem isOpenEmbedding_partial_comp {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : OpenPartialHomeomorph X Y) (f : Z → X) (hf : IsOpenEmbedding f)
    (hmap : ∀ z, f z∈e.source) : IsOpenEmbedding (e ∘ f) := by
  let f' : Z → e.source := fun z => ⟨f z,hmap z⟩
  have hf' : IsOpenEmbedding f' :=
    e.open_source.isOpenEmbedding_subtypeVal.of_comp f' hf
  exact e.isOpenEmbedding_restrict.comp hf'

end TernaryPoly.SymmetricSpaceQuotientBoundary
