module

public import TernaryPeriodPolynomials.Building.Ambient.RelativeNormalForm

@[expose] public section

noncomputable section
namespace TernaryPoly.AmbientRelativePaths
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection BadVertexFibers
open AmbientRelativeProjection AmbientRelativeFibers AmbientRelativeNormalForm
open OrientedListChains

/-- The actual finite signed integer path, already transported to oriented edges. -/
def integerPath (k : ℤ) : Chain ℤ :=
  (IntegerPathChains.edgeTransport (IntegerPathExactness.path k)).val

theorem integerPath_mem (k : ℤ) : integerPath k ∈ chains IntegerPathChains.pathComplex 2 :=
  (IntegerPathChains.edgeTransport (IntegerPathExactness.path k)).property

theorem integerPath_boundary (k : ℤ) :
    boundary (integerPath k) = simplex [k] - simplex [0] := by
  have h := congrArg Subtype.val
    (IntegerPathChains.differential_edgeTransport (IntegerPathExactness.path k))
  change boundary (integerPath k) = _ at h
  rw [h,IntegerPathExactness.boundary_path,map_sub,
    IntegerPathChains.vertexTransport_vertex,IntegerPathChains.vertexTransport_vertex]
  rfl

theorem integerPath_step (k : ℤ) :
    integerPath (k+1) = integerPath k + simplex [k,k+1] := by
  simp only [integerPath,IntegerPathExactness.path_add_one,map_add,
    IntegerPathChains.edgeTransport_edge]
  rfl

theorem integerPath_difference (a b : ℤ) (hab : (a-b).natAbs ≤ 1) :
    integerPath b - integerPath a = simplex [a,b] := by
  have he : a = b ∨ b = a+1 ∨ a = b+1 := by omega
  rcases he with rfl | rfl | rfl
  · rw [sub_self,simplex_repeat_adjacent]
  · rw [integerPath_step,add_sub_cancel_left]
  · rw [integerPath_step,simplex_swap_eq_neg b (b+1)]
    abel

/-- A finite actual path in one prescribed quotient fiber. -/
def fiberPath (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) : Chain RationalLine :=
  OrientedChainMap.map (chart g p hp) (integerPath k)

theorem fiberPath_mem (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    fiberPath g p hp k ∈ chains (link (augmentedLine g 0)) 2 :=
  OrientedChainMap.map_mem_chains _ _ _ (chart_mapsFaces g p hp) 2 (integerPath_mem k)

theorem fiberPath_boundary (g : IntegralGL) (p : Pair) (hp : PairPrimitive p) (k : ℤ) :
    boundary (fiberPath g p hp k) = simplex [chart g p hp k] - simplex [chart g p hp 0] := by
  rw [fiberPath,OrientedChainMap.boundary_map,integerPath_boundary,map_sub]
  simp only [OrientedChainMap.map_simplex,List.map_cons,List.map_nil]

/-- Every finite fiber edge chain cones to every point over an independent quotient neighbor. -/
theorem cone_fiber_edges_mem (g : IntegralGL) (p q : Pair)
    (hp : PairPrimitive p) (hq : PairPrimitive q)
    (hu : IsUnit (p 0 * q 1 - q 0 * p 1)) (l : ℤ)
    {c : Chain ℤ} (hc : c ∈ chains IntegerPathChains.pathComplex 2) :
    cons (chart g q hq l) (OrientedChainMap.map (chart g p hp) c) ∈
      chains (link (augmentedLine g 0)) 3 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨xs,hlen,hxs,rfl⟩ := hc
    obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
    have hf : [a,b].toFinset ∈ IntegerPathChains.pathComplex := by
      convert hxs.resolve_left (by simp) using 1
      ext x
      simp
    obtain ⟨_,k,hk⟩ := hf
    have ha : a = k ∨ a = k+1 := by simpa using hk (by simp)
    have hb : b = k ∨ b = k+1 := by simpa using hk (by simp)
    rw [OrientedChainMap.map_simplex]
    simp only [List.map_cons,List.map_nil,cons_simplex]
    apply simplex_mem_chains (link (augmentedLine g 0))
      [chart g q hq l,chart g p hp a,chart g p hp b] (Or.inr _)
    exact ((link (augmentedLine g 0)).isRelLowerSet_faces (mixed_triangle g p q hp hq hu k l)).2
      (by intro L hL; simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,
          Finset.mem_insert,Finset.mem_singleton] at hL ⊢
          rcases hL with rfl | rfl | rfl
          · exact Or.inr (Or.inr rfl)
          · rcases ha with rfl | rfl <;> simp
          · rcases hb with rfl | rfl <;> simp)
      (by simp)
  | zero => simpa only [map_zero] using (chains (link (augmentedLine g 0)) 3).zero_mem
  | add c d hc hd ihc ihd =>
    simpa only [map_add] using (chains (link (augmentedLine g 0)) 3).add_mem ihc ihd
  | smul r c hc ih =>
    simpa only [map_smul] using (chains (link (augmentedLine g 0)) 3).smul_mem r ih

theorem cone_fiberPath_mem (g : IntegralGL) (p q : Pair)
    (hp : PairPrimitive p) (hq : PairPrimitive q)
    (hu : IsUnit (p 0 * q 1 - q 0 * p 1)) (k l : ℤ) :
    cons (chart g q hq l) (fiberPath g p hp k) ∈ chains (link (augmentedLine g 0)) 3 :=
  cone_fiber_edges_mem g p q hp hq hu l (integerPath_mem k)

/-- Choose primitive quotient directions once, independently of vertex lift. -/
abbrev quotientPair (Q : RankTwoAugmentedFrames.RationalLine2) : Pair :=
  RankTwoHeightLinks.primitiveGenerator Q

abbrev quotientPair_primitive (Q : RankTwoAugmentedFrames.RationalLine2) :
    PairPrimitive (quotientPair Q) := RankTwoHeightLinks.primitiveGenerator_primitive Q

theorem quotientPair_line (Q : RankTwoAugmentedFrames.RationalLine2) :
    quotientLine (quotientPair Q) (quotientPair_primitive Q) = Q :=
  Subtype.ext (RankTwoHeightLinks.primitiveGenerator_span Q)

def canonicalChart (g : IntegralGL) (Q : RankTwoAugmentedFrames.RationalLine2) : ℤ → RationalLine :=
  chart g (quotientPair Q) (quotientPair_primitive Q)

theorem canonicalChart_zero (g : IntegralGL) (Q : RankTwoAugmentedFrames.RationalLine2) :
    canonicalChart g Q 0 = sectionVertex g Q := by
  rw [canonicalChart,← section_quotientLine,quotientPair_line]

theorem exists_coordinate (g : IntegralGL) (L : RationalLine)
    (hL : {L} ∈ link (augmentedLine g 0)) :
    ∃ k, canonicalChart g (vertex g L) k = L := by
  obtain ⟨_,he,ha⟩ := (mem_link _ _).mp hL
  have hedge : {augmentedLine g 0,L} ∈ ambient := by
    convert he using 1
    ext x
    simp
  exact exists_chart g _ _ L (ha L (by simp)) hedge (quotientPair_line _).symm

/-- The coordinate fallback is unused on every actual link vertex. -/
def coordinate (g : IntegralGL) (L : RationalLine) : ℤ := by
  classical
  exact if hL : {L} ∈ link (augmentedLine g 0) then (exists_coordinate g L hL).choose else 0

theorem coordinate_spec (g : IntegralGL) (L : RationalLine)
    (hL : {L} ∈ link (augmentedLine g 0)) :
    canonicalChart g (vertex g L) (coordinate g L) = L := by
  rw [coordinate,dite_eq_left hL]
  exact (exists_coordinate g L hL).choose_spec

/-- A coherent choice of finite paths from the section to every actual link vertex. -/
def vertexPath (g : IntegralGL) (L : RationalLine) : Chain RationalLine :=
  fiberPath g (quotientPair (vertex g L)) (quotientPair_primitive _) (coordinate g L)

theorem vertexPath_mem (g : IntegralGL) (L : RationalLine) :
    vertexPath g L ∈ chains (link (augmentedLine g 0)) 2 := fiberPath_mem _ _ _ _

theorem vertexPath_boundary (g : IntegralGL) (L : RationalLine)
    (hL : {L} ∈ link (augmentedLine g 0)) :
    boundary (vertexPath g L) = simplex [L] - simplex [sectionVertex g (vertex g L)] := by
  rw [vertexPath,fiberPath_boundary]
  change simplex [canonicalChart g (vertex g L) (coordinate g L)] -
    simplex [canonicalChart g (vertex g L) 0] = _
  rw [coordinate_spec g L hL,canonicalChart_zero]

end TernaryPoly.AmbientRelativePaths
