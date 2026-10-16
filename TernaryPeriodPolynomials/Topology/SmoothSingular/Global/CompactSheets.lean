module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ConvexSheets
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingPartition
public import Mathlib.Topology.Compactness.Paracompact

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Filter SymmetricSpaceCovering
open scoped Topology

namespace ConvexSheet

/-- Genuine convex sheets with compact quotient closure form a neighborhood basis. -/
theorem exists_mem_compactClosure_subset {U : Set OrbitSpace} (hU : IsOpen U)
    {q : OrbitSpace} (hq : q ∈ U) :
    ∃ S : ConvexSheet, q ∈ S.quotientDomain ∧ IsCompact (closure S.quotientDomain) ∧
      closure S.quotientDomain ⊆ U := by
  obtain ⟨K,hK,hqK,hKU⟩ := exists_compact_subset hU hq
  obtain ⟨S,hqS,hSK⟩ := exists_mem_subset isOpen_interior hqK
  have hcl : closure S.quotientDomain ⊆ K :=
    closure_minimal (hSK.trans interior_subset) hK.isClosed
  exact ⟨S,hqS,hK.of_isClosed_subset isClosed_closure hcl,hcl.trans hKU⟩

/-- The basis retains convexity of actual lifting sheets and compactness of their closures. -/
theorem compactClosure_nhds_basis (q : OrbitSpace) :
    (𝓝 q).HasBasis (fun S : ConvexSheet => q ∈ S.quotientDomain ∧
      IsCompact (closure S.quotientDomain)) ConvexSheet.quotientDomain := by
  apply (nhds_basis_opens q).to_hasBasis
  · rintro U ⟨hqU,hU⟩
    obtain ⟨S,hqS,hSc,hSU⟩ := exists_mem_compactClosure_subset hU hqU
    exact ⟨S,⟨hqS,hSc⟩,subset_closure.trans hSU⟩
  · intro S hS
    exact ⟨S.quotientDomain,⟨hS.1,S.quotientDomain_isOpen⟩,Subset.rfl⟩

/-- An actual locally finite cover by convex lifting sheets, each with compact quotient closure. -/
theorem exists_locallyFinite_compactClosure_cover :
    ∃ (ι : Type) (S : ι → ConvexSheet),
      (∀ i, IsCompact (closure (S i).quotientDomain)) ∧
      (⋃ i, (S i).quotientDomain) = univ ∧ LocallyFinite (fun i => (S i).quotientDomain) := by
  obtain ⟨ι,c,S,hS,hcover,hfinite⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis compactClosure_nhds_basis
  exact ⟨ι,S,fun i => (hS i).2,hcover,hfinite⟩

end ConvexSheet

/-- Concrete cover data, constructed below, used to control support enlargement by finitely
many actual convex-sheet closures. -/
structure CompactConvexCover where
  Index : Type
  sheet : Index → ConvexSheet
  compactClosure : ∀ i, IsCompact (closure (sheet i).quotientDomain)
  covers : (⋃ i, (sheet i).quotientDomain) = univ
  locallyFinite : LocallyFinite (fun i => (sheet i).quotientDomain)

/-- A selected genuine locally finite relatively compact convex-sheet cover of the quotient. -/
def compactConvexCover : CompactConvexCover := Classical.choice (by
  obtain ⟨ι,S,hS,hcover,hfinite⟩ := ConvexSheet.exists_locallyFinite_compactClosure_cover
  exact ⟨⟨ι,S,hS,hcover,hfinite⟩⟩)

namespace CompactConvexCover

/-- The closed cover star of a set, with actual closure domains as the summands. -/
def star (C : CompactConvexCover) (K : Set OrbitSpace) : Set OrbitSpace :=
  ⋃ (i : C.Index) (_ : ((C.sheet i).quotientDomain ∩ K).Nonempty),
    closure (C.sheet i).quotientDomain

theorem star_isCompact (C : CompactConvexCover) {K : Set OrbitSpace} (hK : IsCompact K) :
    IsCompact (C.star K) :=
  (C.locallyFinite.finite_nonempty_inter_compact hK).isCompact_biUnion
    (fun i _ => C.compactClosure i)

theorem subset_star (C : CompactConvexCover) (K : Set OrbitSpace) : K ⊆ C.star K := by
  intro q hq
  obtain ⟨i,hi⟩ := mem_iUnion.mp (show q ∈ ⋃ i, (C.sheet i).quotientDomain by rw [C.covers]; trivial)
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨q,hi,hq⟩,subset_closure hi⟩⟩

theorem star_mono (C : CompactConvexCover) {K L : Set OrbitSpace} (hKL : K ⊆ L) :
    C.star K ⊆ C.star L := by
  intro q hq
  obtain ⟨i,hi,hq⟩ := mem_iUnion₂.mp hq
  obtain ⟨x,hxi,hxK⟩ := hi
  exact mem_iUnion₂.mpr ⟨i,⟨x,hxi,hKL hxK⟩,hq⟩

theorem closure_subset_star (C : CompactConvexCover) {K : Set OrbitSpace} (i : C.Index)
    (hi : ((C.sheet i).quotientDomain ∩ K).Nonempty) :
    closure (C.sheet i).quotientDomain ⊆ C.star K := by
  intro q hq
  exact mem_iUnion₂.mpr ⟨i,hi,hq⟩

end CompactConvexCover
end TernaryPoly.SmoothSingularGlobal
