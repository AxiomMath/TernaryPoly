module

public import TernaryPeriodPolynomials.Topology.Rational.Compact.NeighborhoodRelative
public import TernaryPeriodPolynomials.Topology.Rational.Compact.NeighborhoodCarriers

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalCompactNeighborhood
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology RationalRelativeSingular

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

/-- Every class supported on a compact set lifts to a compact neighborhood inside any
prescribed open neighborhood, through the actual identity map of relative pairs. -/
theorem exists_compact_lift_within (K U : Set X) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) (c : (supportChains K).homology n) :
    ∃ (L : Set X) (_ : IsCompact L) (hKL : K ⊆ interior L) (_ : L ⊆ U)
      (cL : (supportChains L).homology n),
      homologyMap (restriction L K (hKL.trans interior_subset)) n cL = c := by
  obtain ⟨a, ha, rfl⟩ := exists_projected_cycleClass K n c
  obtain ⟨L, hL, hKL, hLU, hb⟩ := exists_compact_neighborhood_avoiding_chain K U hK hU hKU
    (n-1) ((chains X).d n (n-1) a) ((projected_cycle_iff K n a).mp ha)
  have hcycle := (projected_cycle_iff L n a).mpr hb
  exact ⟨L, hL, hKL, hLU,
    cycleClass (supportChains L) n ((supportProjection L).f n a) hcycle,
    restriction_cycleClass L K (hKL.trans interior_subset) n a hcycle ha⟩

/-- Compact-support relative homology is continuous under compact neighborhoods:
every compact-support class comes from an actual compact neighborhood class. -/
theorem exists_compact_lift (K : Set X) (hK : IsCompact K)
    (n : ℕ) (c : (supportChains K).homology n) :
    ∃ (L : Set X) (_ : IsCompact L) (hKL : K ⊆ interior L)
      (cL : (supportChains L).homology n),
      homologyMap (restriction L K (hKL.trans interior_subset)) n cL = c := by
  obtain ⟨L, hL, hKL, _, cL, hcL⟩ := exists_compact_lift_within K Set.univ hK isOpen_univ
    (Set.subset_univ K) n c
  exact ⟨L, hL, hKL, cL, hcL⟩

/-- A class which vanishes on compact K already vanishes on a compact neighborhood
of K inside its original support. The original support need not itself be compact. -/
theorem exists_compact_zero_witness (K L : Set X) (hK : IsCompact K)
    (hKL : K ⊆ interior L) (n : ℕ) (c : (supportChains L).homology n)
    (hc : homologyMap (restriction L K (hKL.trans interior_subset)) n c = 0) :
    ∃ (K' : Set X) (_ : IsCompact K') (_ : K ⊆ interior K') (hK'L : K' ⊆ L),
      homologyMap (restriction L K' hK'L) n c = 0 := by
  obtain ⟨a, ha, rfl⟩ := exists_projected_cycleClass L n c
  have haK := restricted_cycle L K (hKL.trans interior_subset) n a ha
  rw [restriction_cycleClass L K (hKL.trans interior_subset) n a ha haK] at hc
  obtain ⟨b, e, he⟩ := (projected_cycleClass_eq_zero_iff K n a haK).mp hc
  obtain ⟨K', hK', hKK', hK'L, he'⟩ := exists_compact_neighborhood_avoiding_chain K
    (interior L) hK isOpen_interior hKL n (a - (chains X).d (n+1) n b) ⟨e, he⟩
  have hsub : K' ⊆ L := hK'L.trans interior_subset
  have haK' := restricted_cycle L K' hsub n a ha
  refine ⟨K', hK', hKK', hsub, ?_⟩
  rw [restriction_cycleClass L K' hsub n a ha haK']
  exact (projected_cycleClass_eq_zero_iff K' n a haK').mpr ⟨b, he'⟩

/-- Equality after restriction to compact K has a finite compact-neighborhood witness. -/
theorem exists_compact_equality_witness (K L : Set X) (hK : IsCompact K)
    (hKL : K ⊆ interior L) (n : ℕ) (c d : (supportChains L).homology n)
    (hcd : homologyMap (restriction L K (hKL.trans interior_subset)) n c =
      homologyMap (restriction L K (hKL.trans interior_subset)) n d) :
    ∃ (K' : Set X) (_ : IsCompact K') (_ : K ⊆ interior K') (hK'L : K' ⊆ L),
      homologyMap (restriction L K' hK'L) n c = homologyMap (restriction L K' hK'L) n d := by
  have hz : homologyMap (restriction L K (hKL.trans interior_subset)) n (c-d) = 0 := by
    rw [map_sub, hcd, sub_self]
  obtain ⟨K', hK', hKK', hK'L, he⟩ := exists_compact_zero_witness K L hK hKL n (c-d) hz
  exact ⟨K', hK', hKK', hK'L, sub_eq_zero.mp ((map_sub _ c d).symm.trans he)⟩

/-- A zero local value at an interior point forces zero on a smaller compact
neighborhood support of that point, with the actual restriction map. -/
theorem exists_local_zero_witness (L : Set X) (x : X) (hx : x ∈ interior L)
    (n : ℕ) (c : (supportChains L).homology n)
    (hc : homologyMap (restriction L {x} (by simpa using interior_subset hx)) n c = 0) :
    ∃ (K' : Set X) (_ : IsCompact K') (_ : x ∈ interior K') (hK'L : K' ⊆ L),
      homologyMap (restriction L K' hK'L) n c = 0 := by
  obtain ⟨K', hK', hxK', hK'L, he⟩ := exists_compact_zero_witness {x} L
    (isCompact_singleton) (by simpa using hx) n c hc
  exact ⟨K', hK', hxK' (Set.mem_singleton x), hK'L, he⟩

end TernaryPoly.RationalCompactNeighborhood
