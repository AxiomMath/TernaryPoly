module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactSheets
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechDomains
public import Mathlib.Data.Fintype.Pi

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set SymmetricSpaceCovering

namespace CompactConvexCover

/-- The finite collection of cover indices meeting a compact set. -/
theorem finite_meeting (C : CompactConvexCover) {K : Set OrbitSpace} (hK : IsCompact K) :
    {i | ((C.sheet i).quotientDomain ∩ K).Nonempty}.Finite :=
  C.locallyFinite.finite_nonempty_inter_compact hK

/-- A finite collection of cover members has compact union of its actual closures. -/
theorem finite_closedUnion_isCompact (C : CompactConvexCover) {I : Set C.Index} (hI : I.Finite) :
    IsCompact (⋃ i ∈ I, closure (C.sheet i).quotientDomain) :=
  hI.isCompact_biUnion (fun i _ => C.compactClosure i)

/-- Only finitely many genuine nonempty Čech cofaces can meet a finite tuple collection.
Compact closures and local finiteness control the new index inserted by a face map. -/
theorem finite_cofaces (C : CompactConvexCover) (n : ℕ) {T : Set (Fin (n+1) → C.Index)}
    (hT : T.Finite) :
    {t : Fin (n+2) → C.Index | (cechDomain (fun i => (C.sheet i).quotientDomain) t).Nonempty ∧
      ∃ a : Fin (n+2), t ∘ a.succAbove ∈ T}.Finite := by
  let I : Set C.Index := ⋃ t ∈ T, Set.range t
  have hI : I.Finite := hT.biUnion (fun t _ => finite_range t)
  let K : Set OrbitSpace := ⋃ i ∈ I, closure (C.sheet i).quotientDomain
  have hK : IsCompact K := C.finite_closedUnion_isCompact hI
  let J : Set C.Index := {i | ((C.sheet i).quotientDomain ∩ K).Nonempty}
  have hJ : J.Finite := C.finite_meeting hK
  apply (Set.Finite.pi' (fun _ : Fin (n+2) => hJ)).subset
  intro t ht j
  obtain ⟨⟨x,hxt⟩,a,ha⟩ := ht
  have hi : t (a.succAbove 0) ∈ I :=
    mem_iUnion₂.mpr ⟨t ∘ a.succAbove,ha,mem_range.mpr ⟨0,rfl⟩⟩
  have hxK : x ∈ K := mem_iUnion₂.mpr
    ⟨t (a.succAbove 0),hi,subset_closure (mem_iInter.mp hxt (a.succAbove 0))⟩
  exact ⟨x,mem_iInter.mp hxt j,hxK⟩

/-- All tuples whose actual intersection meets a compact set use only finitely many indices. -/
theorem finite_tuples_meeting (C : CompactConvexCover) (n : ℕ) {K : Set OrbitSpace}
    (hK : IsCompact K) :
    {t : Fin n → C.Index |
      (cechDomain (fun i => (C.sheet i).quotientDomain) t ∩ K).Nonempty}.Finite := by
  apply (Set.Finite.pi' (fun _ : Fin n => C.finite_meeting hK)).subset
  intro t ht i
  obtain ⟨x,hxt,hxK⟩ := ht
  exact ⟨x,mem_iInter.mp hxt i,hxK⟩

end CompactConvexCover
end TernaryPoly.SmoothSingularGlobal
