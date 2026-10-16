module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactData
public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactRefinement

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex RationalLocalOrientation RationalLocalChartHomology
variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- Finite compact gluing requires local data for every compact subset of each piece. The new-piece intersection is itself one such compact subset, so no good-cover condition is needed. -/
theorem finite_family_data (d : ℕ) (g : ∀ x : X, (localChains x).homology d)
    {ι : Type*} (s : Finset ι) (L : ι → Set X) (hL : ∀ i ∈ s, IsCompact (L i))
    (hlocal : ∀ i ∈ s, ∀ K : Set X, IsCompact K → K ⊆ L i → LocalFundamentalData d g K) :
    LocalFundamentalData d g (⋃ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on generalizing L with
  | empty => simpa using empty_data d g
  | @insert i s hi ih =>
    have hLi := hL i (Finset.mem_insert_self i s)
    have hKi := hlocal i (Finset.mem_insert_self i s)
    have hs := ih L (fun j hj => hL j (Finset.mem_insert_of_mem hj))
      (fun j hj => hlocal j (Finset.mem_insert_of_mem hj))
    have hA := hKi (L i) hLi Set.Subset.rfl
    have hAB := hKi (L i ∩ ⋃ j ∈ s, L j) (hLi.inter hs.compact) Set.inter_subset_left
    simpa using union_data d g (L i) (⋃ j ∈ s, L j) hA hs hAB

/-- Actual compact-support fundamental data are local on a locally compact Hausdorff space. -/
theorem compact_data_of_local [LocallyCompactSpace X] (d : ℕ)
    (g : ∀ x : X, (localChains x).homology d) (K : Set X) (hK : IsCompact K)
    (hlocal : ∀ x : X, ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      ∀ L : Set X, IsCompact L → L ⊆ U → LocalFundamentalData d g L) :
    LocalFundamentalData d g K := by
  classical
  choose U hxU hU using hlocal
  obtain ⟨s, L, hLc, _hLK, hLU, hcover⟩ := finite_compact_refinement K hK (fun x : K => U x) (fun x => hxU x)
  have hd := finite_family_data d g s L hLc (fun x hx A hA hAL => hU x A hA (hAL.trans (hLU x hx)))
  rwa [hcover] at hd

end TernaryPoly.RationalManifoldCompact
