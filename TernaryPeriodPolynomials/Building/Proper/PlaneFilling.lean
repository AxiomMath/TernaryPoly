module

public import TernaryPeriodPolynomials.Building.Proper.PlaneGood
public import TernaryPeriodPolynomials.Building.RankTwo.GoodFilling

@[expose] public section


noncomputable section
namespace TernaryPoly.ProperPlaneFilling
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection AmbientRelativeProjection
open ProperPlaneChart ProperPlaneFaces ProperPlaneGood OrientedListChains

/-- Projection followed by section fixes every actual plane-supported chain. -/
theorem section_projection_chain (g : IntegralGL) (n : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains (ProperPlaneFaces.planeComplex g) n) :
    OrientedChainMap.map (sectionVertex g) (OrientedChainMap.map (vertex g) c) = c := by
  let : DecidableEq RationalLine := Classical.decEq _
  rw [OrientedChainMap.map_comp_apply]
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    rw [OrientedChainMap.map_simplex]
    congr 1
    trans l.map id
    · apply List.map_congr_left
      intro L hL
      rcases hl with rfl | hl
      · simp at hL
      · exact section_vertex g L (hl.2 L (List.mem_toFinset.mpr hL))
    · exact List.map_id l
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,ih]

/-- Every actual Good plane one-cycle bounds actual Good triangles in the same plane. -/
theorem one_cycle_filling (g : IntegralGL) {c : Chain RationalLine}
    (hc : c ∈ chains (goodPlane g) 2) (hd : boundary c = 0) :
    ∃ b : Chain RationalLine, b ∈ chains (goodPlane g) 3 ∧ boundary b = c := by
  have hp := OrientedChainMap.map_mem_chains _ _ _ (good_projection_mapsFaces g) 2 hc
  have hdp : boundary (OrientedChainMap.map (vertex g) c) = 0 := by
    rw [OrientedChainMap.boundary_map,hd,map_zero]
  obtain ⟨b,hb,hdb⟩ := RankTwoGoodOne.one_cycle_filling (planeFunctional g) hp hdp
  refine ⟨OrientedChainMap.map (sectionVertex g) b,
    OrientedChainMap.map_mem_chains _ _ _ (good_section_mapsFaces g) 3 hb,?_⟩
  rw [OrientedChainMap.boundary_map,hdb]
  exact section_projection_chain g 2 (chains_mono (goodPlane_le_planeComplex g) 2 hc)

/-- The same literal chart transports reduced Good H0 when the plane covector is nonzero. -/
theorem zero_cycle_filling (g : IntegralGL) (hg : planeFunctional g ≠ 0) {c : Chain RationalLine}
    (hc : c ∈ chains (goodPlane g) 1) (hd : boundary c = 0) :
    ∃ b : Chain RationalLine, b ∈ chains (goodPlane g) 2 ∧ boundary b = c := by
  have hp := OrientedChainMap.map_mem_chains _ _ _ (good_projection_mapsFaces g) 1 hc
  have hdp : boundary (OrientedChainMap.map (vertex g) c) = 0 := by
    rw [OrientedChainMap.boundary_map,hd,map_zero]
  obtain ⟨b,hb,hdb⟩ := RankTwoGoodFilling.zero_cycle_filling (planeFunctional g) hg hp hdp
  refine ⟨OrientedChainMap.map (sectionVertex g) b,
    OrientedChainMap.map_mem_chains _ _ _ (good_section_mapsFaces g) 2 hb,?_⟩
  rw [OrientedChainMap.boundary_map,hdb]
  exact section_projection_chain g 1 (chains_mono (goodPlane_le_planeComplex g) 1 hc)

/-- Actual Good plane triangles have injective boundary. -/
theorem top_boundary_injective (g : IntegralGL) {c d : Chain RationalLine}
    (hc : c ∈ chains (goodPlane g) 3) (hd : d ∈ chains (goodPlane g) 3)
    (he : boundary c = boundary d) : c = d := by
  have hc' := OrientedChainMap.map_mem_chains _ _ _ (good_projection_mapsFaces g) 3 hc
  have hd' := OrientedChainMap.map_mem_chains _ _ _ (good_projection_mapsFaces g) 3 hd
  have he' : boundary (OrientedChainMap.map (vertex g) c) =
      boundary (OrientedChainMap.map (vertex g) d) := by
    rw [OrientedChainMap.boundary_map,OrientedChainMap.boundary_map,he]
  have hh := congrArg (OrientedChainMap.map (sectionVertex g))
    (RankTwoGoodComplex.top_boundary_injective (planeFunctional g) hc' hd' he')
  rwa [section_projection_chain g 3 (chains_mono (goodPlane_le_planeComplex g) 3 hc),
    section_projection_chain g 3 (chains_mono (goodPlane_le_planeComplex g) 3 hd)] at hh

/-- A supported nondegenerate edge supplies the required integral chart for a rational plane. -/
theorem exists_chart_for_plane_edge (P : RationalSubspace) (hP : Module.finrank ℚ P = 2)
    (L M : RationalLine) (hne : L ≠ M)
    (he : {L,M} ∈ ProperPlaneComplex.planeComplex P) : ∃ g : IntegralGL, plane g = P := by
  obtain ⟨g,hg⟩ := exists_plane_of_edge L M hne he.1.1
  refine ⟨g,Submodule.eq_of_le_of_finrank_eq ?_ ((plane_finrank g).trans hP.symm)⟩
  rw [hg]
  exact sup_le (he.2 L (by simp)) (he.2 M (by simp))

/-- A plane with no nondegenerate Good edges carries no nonzero actual one-chains. -/
theorem one_chain_zero_of_no_edge (P : RationalSubspace)
    (hP : ¬∃ L M : RationalLine, L ≠ M ∧ {L,M} ∈ ProperPlaneComplex.planeComplex P)
    {c : Chain RationalLine} (hc : c ∈ chains (ProperPlaneComplex.planeComplex P) 2) : c = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    by_cases hLM : L = M
    · subst M
      exact simplex_repeat_adjacent L []
    · exfalso
      apply hP
      refine ⟨L,M,hLM,?_⟩
      convert hl.resolve_left (by simp) using 1
      ext x
      simp
  | zero => rfl
  | add c d hc hd ihc ihd => rw [ihc,ihd,add_zero]
  | smul q c hc ih => rw [ih,smul_zero]

/-- Unconditional actual Good H1 in every rational plane; only supported planes need an integral chart. -/
theorem arbitrary_plane_one_cycle_filling (P : RationalSubspace) (hP : Module.finrank ℚ P = 2)
    {c : Chain RationalLine} (hc : c ∈ chains (ProperPlaneComplex.planeComplex P) 2)
    (hd : boundary c = 0) :
    ∃ b : Chain RationalLine, b ∈ chains (ProperPlaneComplex.planeComplex P) 3 ∧ boundary b = c := by
  by_cases he : ∃ L M : RationalLine, L ≠ M ∧ {L,M} ∈ ProperPlaneComplex.planeComplex P
  · obtain ⟨L,M,hLM,hface⟩ := he
    obtain ⟨g,hg⟩ := exists_chart_for_plane_edge P hP L M hLM hface
    subst P
    exact one_cycle_filling g hc hd
  · have hz := one_chain_zero_of_no_edge P he hc
    exact ⟨0,(chains _ 3).zero_mem,by rw [map_zero,hz]⟩

/-- The exact plane-filling input consumed by finite proper-span kernel assembly. -/
theorem perPlaneFilling : ProperPlaneComplex.PerPlaneFilling :=
  fun P hP _ hc hd => arbitrary_plane_one_cycle_filling P hP hc hd

end TernaryPoly.ProperPlaneFilling
