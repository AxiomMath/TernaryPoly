module

public import TernaryPeriodPolynomials.Building.Ambient.RelativePaths

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientRelativeHomotopy
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection BadVertexFibers
open AmbientRelativeProjection AmbientRelativeFibers AmbientRelativeNormalForm AmbientRelativePaths
open OrientedListChains OrientedChainJoin

/-- Endpoints of an actual link edge are actual link vertices. -/
theorem edge_vertices (g : IntegralGL) (L M : RationalLine)
    (he : {L,M} ∈ link (augmentedLine g 0)) :
    {L} ∈ link (augmentedLine g 0) ∧ {M} ∈ link (augmentedLine g 0) := by
  constructor
  · exact ((link _).isRelLowerSet_faces he).2 (by intro x hx; simp only [Finset.mem_singleton] at hx; simp [hx]) (by simp)
  · exact ((link _).isRelLowerSet_faces he).2 (by intro x hx; simp only [Finset.mem_singleton] at hx; simp [hx]) (by simp)

/-- On one quotient fiber the coherent path difference is exactly the original edge. -/
theorem same_fiber_path_difference (g : IntegralGL) (L M : RationalLine)
    (he : {L,M} ∈ link (augmentedLine g 0)) (hQ : vertex g L = vertex g M) :
    vertexPath g M - vertexPath g L = simplex [L,M] := by
  obtain ⟨hL,hM⟩ := edge_vertices g L M he
  have ha := coordinate_spec g L hL
  have hb : canonicalChart g (vertex g L) (coordinate g M) = M := by
    rw [hQ]
    exact coordinate_spec g M hM
  have hadj : (coordinate g L-coordinate g M).natAbs ≤ 1 := by
    apply same_fiber_adjacent g (quotientPair (vertex g L)) (quotientPair_primitive _)
    change {canonicalChart g (vertex g L) (coordinate g L),
      canonicalChart g (vertex g L) (coordinate g M)} ∈ link (augmentedLine g 0)
    rw [ha,hb]
    exact he
  change OrientedChainMap.map (canonicalChart g (vertex g M)) (integerPath (coordinate g M)) -
    OrientedChainMap.map (canonicalChart g (vertex g L)) (integerPath (coordinate g L)) = _
  rw [← hQ,← map_sub,integerPath_difference _ _ hadj,OrientedChainMap.map_simplex]
  change simplex [canonicalChart g (vertex g L) (coordinate g L),
    canonicalChart g (vertex g L) (coordinate g M)] = _
  rw [ha,hb]

/-- Each actual edge is homologous to its section edge, with coherent endpoint paths. -/
theorem edge_filling (g : IntegralGL) (L M : RationalLine)
    (he : {L,M} ∈ link (augmentedLine g 0)) :
    ∃ b : Chain RationalLine, b ∈ chains (link (augmentedLine g 0)) 3 ∧
      boundary b = simplex [L,M] -
        simplex [sectionVertex g (vertex g L),sectionVertex g (vertex g M)] -
        vertexPath g M + vertexPath g L := by
  obtain ⟨hL,hM⟩ := edge_vertices g L M he
  by_cases hQ : vertex g L = vertex g M
  · refine ⟨0,(chains (link _) 3).zero_mem,?_⟩
    have hd := same_fiber_path_difference g L M he hQ
    rw [hQ,simplex_repeat_adjacent,map_zero]
    rw [← hd]
    abel
  · have hproj : {vertex g L,vertex g M} ∈ RankTwoAugmentedFrames.ambient := by
      have hh := projection_mapsFaces g _ he
      convert hh using 1
      ext Q
      simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_image]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨L,Or.inl rfl,rfl⟩
        · exact ⟨M,Or.inr rfl,rfl⟩
      · rintro ⟨N,hN,rfl⟩
        rcases hN with rfl | rfl <;> simp
    let p := quotientPair (vertex g L)
    let q := quotientPair (vertex g M)
    have hp : PairPrimitive p := quotientPair_primitive _
    have hq : PairPrimitive q := quotientPair_primitive _
    have hu : IsUnit (p 0 * q 1 - q 0 * p 1) := by
      apply pair_det_isUnit p q hp hq
      · simpa only [p,q,quotientPair_line] using hQ
      · simpa only [p,q,quotientPair_line] using hproj
    have hu' : IsUnit (q 0 * p 1 - p 0 * q 1) := by
      convert hu.neg using 1
      ring
    have hb₁ : cons M (vertexPath g L) ∈ chains (link (augmentedLine g 0)) 3 := by
      have hh := cone_fiberPath_mem g p q hp hq hu (coordinate g L) (coordinate g M)
      change cons (canonicalChart g (vertex g M) (coordinate g M)) (vertexPath g L) ∈ _ at hh
      rw [coordinate_spec g M hM] at hh
      exact hh
    have hb₂ : cons (sectionVertex g (vertex g L)) (vertexPath g M) ∈
        chains (link (augmentedLine g 0)) 3 := by
      have hh := cone_fiberPath_mem g q p hq hp hu' (coordinate g M) 0
      change cons (canonicalChart g (vertex g L) 0) (vertexPath g M) ∈ _ at hh
      rw [canonicalChart_zero] at hh
      exact hh
    refine ⟨cons M (vertexPath g L)-cons (sectionVertex g (vertex g L)) (vertexPath g M),
      (chains (link _) 3).sub_mem hb₁ hb₂,?_⟩
    rw [map_sub,boundary_cons_chain,boundary_cons_chain,
      vertexPath_boundary g L hL,vertexPath_boundary g M hM,map_sub,map_sub]
    simp only [cons_simplex]
    rw [simplex_swap_eq_neg M L [],simplex_swap_eq_neg M (sectionVertex g (vertex g L)) []]
    abel

/-- The endpoint path assignment descends through the actual alternating quotient. -/
def pathValue (g : IntegralGL) : List RationalLine → Chain RationalLine
  | [L] => vertexPath g L
  | _ => 0

theorem pathValue_alternating (g : IntegralGL) :
    SpanChainComparison.AlternatingLists (pathValue g) := by
  intro p a b s
  cases p with
  | nil => simp [pathValue]
  | cons n p => cases p <;> simp [pathValue]

def pathMap (g : IntegralGL) : Chain RationalLine →ₗ[ℚ] Chain RationalLine :=
  SpanChainComparison.evaluate (pathValue g) (pathValue_alternating g)

@[simp] theorem pathMap_singleton (g : IntegralGL) (L : RationalLine) :
    pathMap g (simplex [L]) = vertexPath g L :=
  SpanChainComparison.evaluate_simplex _ _ _

theorem pathMap_boundary_edge (g : IntegralGL) (L M : RationalLine) :
    pathMap g (boundary (simplex [L,M])) = vertexPath g M - vertexPath g L := by
  simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex,map_sub,pathMap_singleton]

/-- The edge homotopies extend to every finite actual one-chain. -/
theorem chain_homotopy (g : IntegralGL) {c : Chain RationalLine}
    (hc : c ∈ chains (link (augmentedLine g 0)) 2) :
    ∃ b : Chain RationalLine, b ∈ chains (link (augmentedLine g 0)) 3 ∧
      boundary b = c - OrientedChainMap.map (sectionVertex g ∘ vertex g) c -
        pathMap g (boundary c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    have hface : {L,M} ∈ link (augmentedLine g 0) := by
      convert hl.resolve_left (by simp) using 1
      ext x
      simp
    obtain ⟨b,hb,hdb⟩ := edge_filling g L M hface
    refine ⟨b,hb,?_⟩
    rw [pathMap_boundary_edge,OrientedChainMap.map_simplex]
    simp only [List.map_cons,List.map_nil,Function.comp_apply]
    rw [hdb]
    abel
  | zero => exact ⟨0,(chains (link _) 3).zero_mem,by simp only [map_zero,sub_zero]⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨b,hb,hdb⟩ := ihc
    obtain ⟨e,he,hde⟩ := ihd
    refine ⟨b+e,(chains (link _) 3).add_mem hb he,?_⟩
    rw [map_add,hdb,hde,map_add,map_add,map_add]
    abel
  | smul r c hc ih =>
    obtain ⟨b,hb,hdb⟩ := ih
    refine ⟨r • b,(chains (link _) 3).smul_mem r hb,?_⟩
    rw [map_smul,hdb,map_smul,map_smul,map_smul,smul_sub,smul_sub]

end TernaryPoly.AmbientRelativeHomotopy
