module

public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Cross

@[expose] public section


/-!
# Lemma A.1, items 2 and 3: connectedness and `H₁(L_b; ℚ) = 0`

Formalized by Claude Sonnet 5.5.
Paper: Lemma A.1.

The projection `p : L_b → Z` carries a cycle `c` of `L_b` to a cycle of the good rank-two complex
`Z`, which is acyclic (`RankTwoGoodFilling.good_exactness`).  Lifting the filling to `L_b`
(`lift_chain`) and subtracting its boundary leaves a cycle with zero projection.  Such a cycle is
filled fibrewise: over a base vertex by the contractible path `P_u` (`vertex_component_fill`,
`fiber_cycle_zero`), over a base edge by the mixed triangles of the join `P_u * P_v`
(`cross_component_reduce`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixALink

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction TernaryPoly.CoherentPrismReduction
  TernaryPoly.BadVertexProjection TernaryPoly.OrientedImageFaceProjection
  TernaryPoly.OrientedImageFaceBoundary TernaryPoly.OrientedImageFaceDecomposition

local instance instDecRLA : DecidableEq RationalLine := Classical.decEq _
local instance instDecRLTwoA : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _
local notation "res" => AugmentedPrismCaps.columnResidue

/-- A projected-zero zero-chain of the link is a boundary in the link. -/
theorem fiber0 (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val) {c : Chain RationalLine}
    (hc : c ∈ chains (badLink (augmentedLine g 0)) 1)
    (hz : OrientedChainMap.map (vertex g) c = 0) :
    ∃ t ∈ chains (badLink (augmentedLine g 0)) 2, boundary t = c := by
  classical
  refine fill_of_components (vertex g) (chains (badLink (augmentedLine g 0)) 2) c ?_
  intro s
  by_cases hne : project (vertex g) s c = 0
  · exact ⟨0,Submodule.zero_mem _,by rw [hne,map_zero]⟩
  obtain ⟨l,hlen,hl,_,hs⟩ := BadVertexFaceCharts.exists_supported_simplex (vertex g) _ 1 s hc hne
  obtain ⟨Q,rfl⟩ := List.length_eq_one_iff.mp hlen
  have hQ : ({Q} : Finset RationalLine) ∈ badLink (augmentedLine g 0) := by
    have := hl.resolve_left (by simp)
    convert this using 1
    simp
  obtain ⟨h,hh,_,hx,hqc⟩ := exists_chart_vertex g hbad Q hQ
  have hbad_h : ¬Good (augmentedLine h 0).val := by rw [hh]; exact hbad
  have hs' : s = ({A0} : Finset RankTwoAugmentedFrames.RationalLine2).image
      (BadVertexProjectionChange.quotientChange g h hh) := by
    rw [← hs,Finset.image_singleton,← hqc]
    simp [imageFace]
  have hc_h : c ∈ chains (badLink (augmentedLine h 0)) 1 := by rwa [hh]
  have hz_h : OrientedChainMap.map (vertex h) c = 0 :=
    (BadVertexProjectionChange.map_eq_zero_change g h hh hbad 1 hc).mp hz
  obtain ⟨t,ht,hdt⟩ := vertex_component_fill h hbad_h hx hc_h hz_h
  refine ⟨t,by rwa [hh] at ht,?_⟩
  rw [hdt,hs',BadVertexProjectionChange.project_change g h hh hbad {A0} 1 hc]

/-- A cycle of the link which is supported over single quotient vertices vanishes, as the
fibre paths have no cycles. -/
theorem fiber_cycle_zero_global (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {F : Chain RationalLine} (hF : F ∈ chains (badLink (augmentedLine g 0)) 2)
    (him : F ∈ imageBounded (vertex g) 1) (hd : boundary F = 0) : F = 0 := by
  classical
  obtain ⟨S,hS,_⟩ := exists_decomposition (vertex g) F
  rw [← hS]
  apply Finset.sum_eq_zero
  intro s _
  by_contra hne
  obtain ⟨l,hlen,hl,_,hs⟩ := BadVertexFaceCharts.exists_supported_simplex (vertex g) _ 2 s hF hne
  obtain ⟨Q,R,rfl⟩ := List.length_eq_two.mp hlen
  have hlf : ({Q,R} : Finset RationalLine) ∈ badLink (augmentedLine g 0) := by
    have := hl.resolve_left (by simp)
    convert this using 1
    ext x; simp
  have hQ := singleton_mem_of_mem hlf (by simp : Q ∈ ({Q,R} : Finset RationalLine))
  have hcard : s.card = 1 := by
    have h1 : 1 ≤ s.card := by
      rw [← hs]
      apply Finset.card_pos.mpr
      simp [imageFace]
    by_contra hne1
    exact hne (project_eq_zero_of_card_lt (vertex g) him s (by omega))
  obtain ⟨w,rfl⟩ := Finset.card_eq_one.mp hcard
  obtain ⟨h,hh,_,_,hqc⟩ := exists_chart_vertex g hbad Q hQ
  have hbad_h : ¬Good (augmentedLine h 0).val := by rw [hh]; exact hbad
  have hw : w = BadVertexProjectionChange.quotientChange g h hh A0 := by
    rw [← hqc]
    have : vertex g Q ∈ imageFace (vertex g) [Q,R] :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨Q,by simp,rfl⟩)
    rw [hs] at this
    exact (Finset.mem_singleton.mp this).symm
  have hF_h : F ∈ chains (badLink (augmentedLine h 0)) 2 := by rwa [hh]
  have him_h : F ∈ imageBounded (vertex h) 1 :=
    (BadVertexProjectionChange.imageBounded_change_iff g h hh hbad 2 1 hF).mp him
  apply hne
  have e : ({BadVertexProjectionChange.quotientChange g h hh A0} :
      Finset RankTwoAugmentedFrames.RationalLine2) =
      ({A0} : Finset RankTwoAugmentedFrames.RationalLine2).image
        (BadVertexProjectionChange.quotientChange g h hh) := (Finset.image_singleton _ _).symm
  rw [hw,e,BadVertexProjectionChange.project_change g h hh hbad {A0} 2 hF]
  exact fiber_cycle_zero h hbad_h hF_h him_h hd

/-- A projected-zero one-cycle of the link is a boundary of a two-chain of the link. -/
theorem fiber1 (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val) {c : Chain RationalLine}
    (hc : c ∈ chains (badLink (augmentedLine g 0)) 2) (hd : boundary c = 0)
    (hz : OrientedChainMap.map (vertex g) c = 0) :
    ∃ t ∈ chains (badLink (augmentedLine g 0)) 3, boundary t = c := by
  classical
  have key : ∀ s : Finset RankTwoAugmentedFrames.RationalLine2,
      ∃ t ∈ chains (badLink (augmentedLine g 0)) 3, ∃ f ∈ chains (badLink (augmentedLine g 0)) 2,
        f ∈ imageBounded (vertex g) 1 ∧ project (vertex g) s c = boundary t + f := by
    intro s
    by_cases hne : project (vertex g) s c = 0
    · exact ⟨0,Submodule.zero_mem _,0,Submodule.zero_mem _,Submodule.zero_mem _,by simp [hne]⟩
    obtain ⟨l,hlen,hl,_,hs⟩ :=
      BadVertexFaceCharts.exists_supported_simplex (vertex g) _ 2 s hc hne
    obtain ⟨Q,R,rfl⟩ := List.length_eq_two.mp hlen
    have hlf : ({Q,R} : Finset RationalLine) ∈ badLink (augmentedLine g 0) := by
      have := hl.resolve_left (by simp)
      convert this using 1
      ext x; simp
    by_cases hv : vertex g Q = vertex g R
    · -- both endpoints over one quotient vertex
      refine ⟨0,Submodule.zero_mem _,project (vertex g) s c,project_mem_chains _ _ _ _ hc,?_,by simp⟩
      have hs1 : s.card = 1 := by
        rw [← hs]
        simp [imageFace,hv]
      have := project_mem_imageBounded (vertex g) s c
      rwa [hs1] at this
    · obtain ⟨h,hh,_,_,hx,hy,hqQ,hqR⟩ := exists_chart_edge g hbad Q R hlf hv
      have hbad_h : ¬Good (augmentedLine h 0).val := by rw [hh]; exact hbad
      have hc_h : c ∈ chains (badLink (augmentedLine h 0)) 2 := by rwa [hh]
      have hz_h : OrientedChainMap.map (vertex h) c = 0 :=
        (BadVertexProjectionChange.map_eq_zero_change g h hh hbad 2 hc).mp hz
      obtain ⟨t,ht,f,hf,hfb,he⟩ := cross_component_reduce h hbad_h hx hy hc_h hz_h
      have hs' : s = BadVertexMixedProjection.baseEdge.image
          (BadVertexProjectionChange.quotientChange g h hh) := by
        rw [← hs]
        simp only [BadVertexMixedProjection.baseEdge,Finset.image_insert,Finset.image_singleton,
          ← hqQ,← hqR]
        ext x
        simp [imageFace]
      refine ⟨t,by rwa [hh] at ht,f,by rwa [hh] at hf,
        (BadVertexProjectionChange.imageBounded_change_iff g h hh hbad 2 1 (by rwa [hh] at hf)).mpr hfb,?_⟩
      rw [hs',BadVertexProjectionChange.project_change g h hh hbad _ 2 hc]
      exact he
  choose t ht f hf hfb he using key
  obtain ⟨S,hS,_⟩ := exists_decomposition (vertex g) c
  have hT : ∑ s ∈ S, t s ∈ chains (badLink (augmentedLine g 0)) 3 :=
    Submodule.sum_mem _ (fun s _ => ht s)
  have hF : ∑ s ∈ S, f s ∈ chains (badLink (augmentedLine g 0)) 2 :=
    Submodule.sum_mem _ (fun s _ => hf s)
  have hFb : ∑ s ∈ S, f s ∈ imageBounded (vertex g) 1 := Submodule.sum_mem _ (fun s _ => hfb s)
  have hE : c = boundary (∑ s ∈ S, t s) + ∑ s ∈ S, f s := by
    rw [map_sum,← Finset.sum_add_distrib]
    calc c = ∑ s ∈ S, project (vertex g) s c := hS.symm
      _ = _ := Finset.sum_congr rfl (fun s _ => he s)
  have hFd : boundary (∑ s ∈ S, f s) = 0 := by
    have h := congrArg boundary hE
    rw [map_add,hd,boundary_squared,zero_add] at h
    exact h.symm
  have hF0 := fiber_cycle_zero_global g hbad hF hFb hFd
  refine ⟨∑ s ∈ S, t s,hT,?_⟩
  rw [hE, hF0, add_zero]

end TernaryPeriodPolynomials.Argument.AppendixALink
