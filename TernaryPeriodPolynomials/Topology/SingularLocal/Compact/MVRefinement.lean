module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactRefinement
public import Mathlib.Topology.Sets.Compacts

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open TopologicalSpace

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

/-- Every compact set has an exact decomposition into two compact subsets subordinate to an open cover. -/
theorem compact_binary_refinement (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (S : Set X) (hS : IsCompact S) :
    ∃ K L : Set X, IsCompact K ∧ IsCompact L ∧ K ⊆ S ∧ L ⊆ S ∧
      K ⊆ U ∧ L ⊆ V ∧ K ∪ L = S := by
  classical
  let W : S → Opens X := fun x => if x.val ∈ U then U else V
  have hW : ∀ x : S, x.val ∈ W x := by
    intro x
    dsimp [W]
    split_ifs with hx
    · exact hx
    · have hh : x.val ∈ U ⊔ V := by rw [hUV]; trivial
      exact hh.resolve_left hx
  obtain ⟨s,C,hCc,hCS,hCW,hCover⟩ :=
    RationalManifoldCompact.finite_compact_refinement S hS W hW
  let sU := s.filter (fun x => x.val ∈ U)
  let sV := s.filter (fun x => x.val ∉ U)
  refine ⟨⋃ x ∈ sU, C x,⋃ x ∈ sV, C x,?_,?_,?_,?_,?_,?_,?_⟩
  · exact sU.isCompact_biUnion fun x hx => hCc x (Finset.mem_filter.mp hx).1
  · exact sV.isCompact_biUnion fun x hx => hCc x (Finset.mem_filter.mp hx).1
  · exact Set.iUnion₂_subset fun x hx => hCS x (Finset.mem_filter.mp hx).1
  · exact Set.iUnion₂_subset fun x hx => hCS x (Finset.mem_filter.mp hx).1
  · apply Set.iUnion₂_subset
    intro x hx
    have h := Finset.mem_filter.mp hx
    simpa [W,h.2] using hCW x h.1
  · apply Set.iUnion₂_subset
    intro x hx
    have h := Finset.mem_filter.mp hx
    simpa [W,h.2] using hCW x h.1
  · apply Eq.trans ?_ hCover
    ext x
    simp only [Set.mem_union,Set.mem_iUnion,sU,sV,Finset.mem_filter]
    constructor
    · rintro (⟨y,⟨hy,_⟩,hxy⟩ | ⟨y,⟨hy,_⟩,hxy⟩) <;> exact ⟨y,hy,hxy⟩
    · rintro ⟨y,hy,hxy⟩
      by_cases hyU : y.val ∈ U
      · exact Or.inl ⟨y,⟨hy,hyU⟩,hxy⟩
      · exact Or.inr ⟨y,⟨hy,hyU⟩,hxy⟩

/-- A compact set subordinate to an open subset defines a compact support in the literal subspace. -/
def compactInOpen (U : Opens X) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U) : Compacts U :=
  ⟨(Subtype.val : U → X) ⁻¹' K, by
    apply Topology.IsInducing.isCompact_preimage' Topology.IsEmbedding.subtypeVal.isInducing hK
    exact fun x hx => ⟨⟨x,hKU hx⟩,rfl⟩⟩

end TernaryPoly.SingularLocalCompactMV
