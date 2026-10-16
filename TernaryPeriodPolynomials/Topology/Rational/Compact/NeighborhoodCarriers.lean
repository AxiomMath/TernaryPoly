module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.Singular
public import Mathlib.Topology.Compactness.LocallyCompact

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalCompactNeighborhood
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology RationalRelativeSingular
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

variable {X : Type} [TopologicalSpace X]

/-- Literal subspace-chain membership equals membership in the span of its simplices. -/
theorem inclusion_range_iff (S : Set X) (n : ℕ) (a : (chains X).X n) :
    (∃ b : (chains S).X n, (inclusion S).f n b = a) ↔
      a ∈ subChainSubmodule ℚ (TopCat.of X) S n := by
  constructor
  · rintro ⟨b, rfl⟩
    change (singularChainMap ℚ (sInclusion (X := TopCat.of X) S) n).hom b ∈ _
    exact singularChainMap_sInclusion_mem (R := ℚ) (X := TopCat.of X) S n b
  · intro ha
    obtain ⟨b, hb⟩ := (subChainCorestrict_bijective (R := ℚ) (X := TopCat.of X) S n).surjective
      ⟨a, ha⟩
    exact ⟨b, congrArg Subtype.val hb⟩

/-- Finite span induction gives a compact carrier inside any prescribed chain support.
The generator case uses the compact image of its genuine standard simplex. -/
theorem exists_compact_carrier (S : Set X) (n : ℕ) (a : (chains X).X n)
    (ha : a ∈ subChainSubmodule ℚ (TopCat.of X) S n) :
    ∃ A : Set X, IsCompact A ∧ A ⊆ S ∧
      a ∈ subChainSubmodule ℚ (TopCat.of X) A n := by
  apply subChainSubmodule_induction (c := a) (S := S) (n := n) (R := ℚ) (X := TopCat.of X) ?_ ?_ ?_ ?_ ha
  · intro σ hσ
    exact ⟨Set.range (mvSimplexMap σ), isCompact_range (mvSimplexMap σ).continuous,
      hσ, chainGenerator_mem_subChainSubmodule Set.Subset.rfl⟩
  · exact ⟨∅, isCompact_empty, Set.empty_subset _, Submodule.zero_mem _⟩
  · intro a b ha hb
    obtain ⟨A, hA, hAS, haA⟩ := ha
    obtain ⟨B, hB, hBS, hbB⟩ := hb
    exact ⟨A ∪ B, hA.union hB, Set.union_subset hAS hBS,
      Submodule.add_mem _ (subChainSubmodule_mono Set.subset_union_left n haA)
        (subChainSubmodule_mono Set.subset_union_right n hbB)⟩
  · intro r a ha
    obtain ⟨A, hA, hAS, haA⟩ := ha
    exact ⟨A, hA, hAS, Submodule.smul_mem _ r haA⟩

/-- A compact neighborhood can avoid the finite carrier of a chain in the complement.
The optional open set controls where the neighborhood lies. -/
theorem exists_compact_neighborhood_avoiding_chain [T2Space X] [LocallyCompactSpace X]
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (n : ℕ) (a : (chains X).X n)
    (ha : ∃ b : (chains (Kᶜ : Set X)).X n, (inclusion Kᶜ).f n b = a) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∧
      ∃ b : (chains (Lᶜ : Set X)).X n, (inclusion Lᶜ).f n b = a := by
  obtain ⟨A, hA, hAK, haA⟩ := exists_compact_carrier Kᶜ n a
    ((inclusion_range_iff Kᶜ n a).mp ha)
  have hsub : K ⊆ U ∩ Aᶜ := by
    intro x hx
    exact ⟨hKU hx, fun hxA => hAK hxA hx⟩
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK
    (hU.inter hA.isClosed.isOpen_compl) hsub
  refine ⟨L, hL, hKL, fun x hx => (hLU hx).1, (inclusion_range_iff Lᶜ n a).mpr ?_⟩
  exact subChainSubmodule_mono (fun x hxA hxL => (hLU hxL).2 hxA) n haA

end TernaryPoly.RationalCompactNeighborhood
