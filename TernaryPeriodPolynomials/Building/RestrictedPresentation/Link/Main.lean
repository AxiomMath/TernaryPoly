module

public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Assembly
public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Generation

@[expose] public section


/-!
# Lemma A.1: assembly

Formalized by Claude Sonnet 5.5.
Paper: Lemma A.1
(`lem:bad-link-generators`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixALink

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction TernaryPoly.CoherentPrismReduction
  TernaryPoly.BadVertexProjection

/-- `H̃₀(L_b; ℚ) = 0`: every zero-cycle of the link is the boundary of a one-chain of the link. -/
theorem connected_link (b : RationalLine) (hb : ¬Good b.val) {c : Chain RationalLine}
    (hc : c ∈ chains (badLink b) 1) (hd : boundary c = 0) :
    ∃ t ∈ chains (badLink b) 2, boundary t = c := by
  obtain ⟨g,rfl⟩ := RationalLineBasis.rationalLine_eq_augmentedLine b
  have h1 : OrientedChainMap.map (vertex g) c ∈ chains (RankTwoGoodComplex.good (phi g)) 1 :=
    OrientedChainMap.map_mem_chains _ _ _ (mapsFaces_phi g hb) 1 hc
  have h2 : boundary (OrientedChainMap.map (vertex g) c) = 0 := by
    rw [boundary_transport,hd,map_zero]
  obtain ⟨w,hw,hdw⟩ := (RankTwoGoodFilling.good_exactness (phi g) (phi_ne_zero g hb)).1 _ h1 h2
  obtain ⟨w',hw',hπ⟩ := lift_chain g hb 2 (by norm_num) hw
  have hc' : c - boundary w' ∈ chains (badLink (augmentedLine g 0)) 1 :=
    (chains _ _).sub_mem hc (boundary_mem_chains _ 1 hw')
  have hz : OrientedChainMap.map (vertex g) (c - boundary w') = 0 := by
    rw [map_sub,← OrientedChainMap.boundary_map,hπ,hdw,sub_self]
  obtain ⟨t,ht,hdt⟩ := fiber0 g hb hc' hz
  exact ⟨w' + t,(chains _ _).add_mem hw' ht,by rw [map_add,hdt]; abel⟩

/-- `H₁(L_b; ℚ) = 0`: every one-cycle of the link is the boundary of a two-chain of the link. -/
theorem simply_connected_link (b : RationalLine) (hb : ¬Good b.val) {c : Chain RationalLine}
    (hc : c ∈ chains (badLink b) 2) (hd : boundary c = 0) :
    ∃ t ∈ chains (badLink b) 3, boundary t = c := by
  obtain ⟨g,rfl⟩ := RationalLineBasis.rationalLine_eq_augmentedLine b
  have h1 : OrientedChainMap.map (vertex g) c ∈ chains (RankTwoGoodComplex.good (phi g)) 2 :=
    OrientedChainMap.map_mem_chains _ _ _ (mapsFaces_phi g hb) 2 hc
  have h2 : boundary (OrientedChainMap.map (vertex g) c) = 0 := by
    rw [boundary_transport,hd,map_zero]
  obtain ⟨w,hw,hdw⟩ := (RankTwoGoodFilling.good_exactness (phi g) (phi_ne_zero g hb)).2.1 _ h1 h2
  obtain ⟨w',hw',hπ⟩ := lift_chain g hb 3 (by norm_num) hw
  have hc' : c - boundary w' ∈ chains (badLink (augmentedLine g 0)) 2 :=
    (chains _ _).sub_mem hc (boundary_mem_chains _ 2 hw')
  have hd' : boundary (c - boundary w') = 0 := by
    rw [map_sub,hd,boundary_squared,sub_zero]
  have hz : OrientedChainMap.map (vertex g) (c - boundary w') = 0 := by
    rw [map_sub,← OrientedChainMap.boundary_map,hπ,hdw,sub_self]
  obtain ⟨t,ht,hdt⟩ := fiber1 g hb hc' hd' hz
  exact ⟨w' + t,(chains _ _).add_mem hw' ht,by rw [map_add,hdt]; abel⟩

/-- **Lemma A.1.** -/
theorem lemma_A1 (b : RationalLine) (hb : ¬Good b.val) :
    (∃ a : RationalLine, ({a} : Finset RationalLine) ∈ badLink b) ∧
    (∀ c ∈ chains (badLink b) 1, boundary c = 0 →
      ∃ t ∈ chains (badLink b) 2, boundary t = c) ∧
    (∀ c ∈ chains (badLink b) 2, boundary c = 0 →
      ∃ t ∈ chains (badLink b) 3, boundary t = c) ∧
    (∀ c ∈ chains (badLink b) 3, boundary c = 0 →
      c ∈ Submodule.span ℚ (tetraSpheres b ∪ prismSpheres b)) ∧
    (∀ c ∈ tetraSpheres b ∪ prismSpheres b, c ∈ chains (badLink b) 3 ∧ boundary c = 0) ∧
    chains (badLink b) 4 = ⊥ :=
  ⟨exists_vertex b hb,fun _ hc hd => connected_link b hb hc hd,
    fun _ hc hd => simply_connected_link b hb hc hd,
    fun _ hc hd => generation b hb hc hd,
    fun _ hc => generator_mem b hb hc,chains_four_eq_bot b hb⟩

end TernaryPeriodPolynomials.Argument.AppendixALink
