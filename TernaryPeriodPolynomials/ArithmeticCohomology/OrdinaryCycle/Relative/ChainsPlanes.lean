module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Relative.Chains
public import TernaryPeriodPolynomials.Building.Proper.PlaneFaces
public import TernaryPeriodPolynomials.Building.RankTwo.HeightOne

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryRelativeChainsPlanes
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains OrdinaryRelativeChains
open ProperPlaneChart BadVertexProjection AmbientRelativeProjection
open ProperPlaneFaces

/-- Actual ambient augmented faces contained in one specified rational subspace. -/
def planeComplex (P : RationalSubspace) : PreAbstractSimplicialComplex RationalLine where
  faces := {s | s ∈ ambient ∧ ∀ L ∈ s, L.val ≤ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(ambient.isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨(ambient.isRelLowerSet_faces hs.1).2 hts ht,fun L hL => hs.2 L (hts hL)⟩

theorem planeComplex_le_ambient (P : RationalSubspace) : planeComplex P ≤ ambient := fun _ h => h.1

theorem planeComplex_faceSpan_le (P : RationalSubspace) (s : Finset RationalLine)
    (hs : s ∈ planeComplex P) : faceSpan s ≤ P := Finset.sup_le hs.2

/-- A genuine plane carries only proper-span ambient faces. -/
theorem planeComplex_le_properAmbient (P : RationalSubspace) (hP : Module.finrank ℚ P ≤ 2) :
    planeComplex P ≤ properAmbient := by
  intro s hs
  exact ⟨hs.1,(Submodule.finrank_mono (planeComplex_faceSpan_le P s hs)).trans hP⟩

/-- The precise per-plane H1 input, stated on actual finite ambient simplex chains. -/
def PerPlaneFilling : Prop :=
  ∀ P : RationalSubspace, Module.finrank ℚ P = 2 →
    ∀ c : Chain RationalLine, c ∈ chains (planeComplex P) 2 → boundary c = 0 →
      ∃ b : Chain RationalLine, b ∈ chains (planeComplex P) 3 ∧ boundary b = c

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

/-- Every actual ambient plane one-cycle bounds actual ambient triangles in the same plane. -/
theorem one_cycle_filling (g : IntegralGL) {c : Chain RationalLine}
    (hc : c ∈ chains (ProperPlaneFaces.planeComplex g) 2) (hd : boundary c = 0) :
    ∃ b : Chain RationalLine, b ∈ chains (ProperPlaneFaces.planeComplex g) 3 ∧ boundary b = c := by
  have hp := OrientedChainMap.map_mem_chains _ _ _ (ProperPlaneFaces.projection_mapsFaces g) 2 hc
  have hdp : boundary (OrientedChainMap.map (vertex g) c) = 0 := by
    rw [OrientedChainMap.boundary_map,hd,map_zero]
  obtain ⟨b,hb,hdb⟩ := RankTwoHeightOne.ambient_one_cycle_filling hp hdp
  refine ⟨OrientedChainMap.map (sectionVertex g) b,
    OrientedChainMap.map_mem_chains _ _ _ (ProperPlaneFaces.section_mapsFaces g) 3 hb,?_⟩
  rw [OrientedChainMap.boundary_map,hdb]
  exact section_projection_chain g 2 hc


/-- A supported nondegenerate edge supplies the required integral chart for a rational plane. -/
theorem exists_chart_for_plane_edge (P : RationalSubspace) (hP : Module.finrank ℚ P = 2)
    (L M : RationalLine) (hne : L ≠ M)
    (he : {L,M} ∈ planeComplex P) : ∃ g : IntegralGL, plane g = P := by
  obtain ⟨g,hg⟩ := exists_plane_of_edge L M hne he.1
  refine ⟨g,Submodule.eq_of_le_of_finrank_eq ?_ ((plane_finrank g).trans hP.symm)⟩
  rw [hg]
  exact sup_le (he.2 L (by simp)) (he.2 M (by simp))

/-- A plane with no nondegenerate ambient edges carries no nonzero actual one-chains. -/
theorem one_chain_zero_of_no_edge (P : RationalSubspace)
    (hP : ¬∃ L M : RationalLine, L ≠ M ∧ {L,M} ∈ planeComplex P)
    {c : Chain RationalLine} (hc : c ∈ chains (planeComplex P) 2) : c = 0 := by
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

/-- Unconditional actual ambient H1 in every rational plane; only supported planes need an integral chart. -/
theorem arbitrary_plane_one_cycle_filling (P : RationalSubspace) (hP : Module.finrank ℚ P = 2)
    {c : Chain RationalLine} (hc : c ∈ chains (planeComplex P) 2)
    (hd : boundary c = 0) :
    ∃ b : Chain RationalLine, b ∈ chains (planeComplex P) 3 ∧ boundary b = c := by
  by_cases he : ∃ L M : RationalLine, L ≠ M ∧ {L,M} ∈ planeComplex P
  · obtain ⟨L,M,hLM,hface⟩ := he
    obtain ⟨g,hg⟩ := exists_chart_for_plane_edge P hP L M hLM hface
    subst P
    exact one_cycle_filling g hc hd
  · have hz := one_chain_zero_of_no_edge P he hc
    exact ⟨0,(chains _ 3).zero_mem,by rw [map_zero,hz]⟩


/-- Unrestricted rational-plane H1 follows from the actual rank-two ambient filling. -/
theorem perPlaneFilling : PerPlaneFilling :=
  fun P hP _ hc hd => arbitrary_plane_one_cycle_filling P hP hc hd

end TernaryPoly.OrdinaryRelativeChainsPlanes
