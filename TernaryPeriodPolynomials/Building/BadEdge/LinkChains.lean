module

public import TernaryPeriodPolynomials.Building.BadEdge.LinkGrid
public import TernaryPeriodPolynomials.Building.Good.LinkExtraction
public import TernaryPeriodPolynomials.Building.Integer.Exactness
public import TernaryPeriodPolynomials.Building.Span.ChainComparison

@[expose] public section


/-! Every finite oriented one-cycle in the actual good link of a bad basis edge
is a finite sum of square loops. Squares are loops, not simplicial two-cells. -/

noncomputable section
namespace TernaryPoly.BadEdgeLinkChains
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces BadEdgeLinkVertices
open BadEdgeLinkGrid OrientedListChains

local instance : DecidableEq RationalLine := Classical.decEq _

variable (g : IntegralGL)

def badEdge : Finset RationalLine := {augmentedLine g 0,augmentedLine g 1}
def link : PreAbstractSimplicialComplex RationalLine :=
  GoodLinkExtraction.augmentedGoodLink (badEdge g)

abbrev LinkVertices := chains (link g) 1
abbrev LinkEdges := chains (link g) 2

variable (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
variable (h2 : columnResidue g 2 ≠ 0)

include h0 h1 h2 in
theorem singleton_allowed (p : IntegerGridExactness.Vertex) :
    Allowed (link g) [coordinateLine g p] := by
  apply Or.inr
  obtain ⟨_,k,hk⟩ := coordinateLine_face g p
  refine ⟨⟨by simp,⟨by simp [badEdge],k,?_⟩⟩,?_⟩
  · intro L hL
    apply hk
    simpa [badEdge,or_comm,or_left_comm,or_assoc] using hL
  · intro L hL
    have he : L = coordinateLine g p := by simpa using hL
    subst L
    exact coordinateLine_good g h0 h1 h2 p

include h0 h1 h2 in
theorem pair_allowed (p q : IntegerGridExactness.Vertex) (hpq : GridAdjacent p q) :
    Allowed (link g) [coordinateLine g p,coordinateLine g q] := by
  apply Or.inr
  obtain ⟨_,k,hk⟩ := face_of_gridAdjacent g p q hpq
  refine ⟨⟨by simp,⟨by simp [badEdge],k,?_⟩⟩,?_⟩
  · intro L hL
    apply hk
    simpa [badEdge,or_comm,or_left_comm,or_assoc] using hL
  · intro L hL
    have he : L = coordinateLine g p ∨ L = coordinateLine g q := by simpa using hL
    rcases he with rfl | rfl
    · exact coordinateLine_good g h0 h1 h2 p
    · exact coordinateLine_good g h0 h1 h2 q

/-- Each literal grid unit edge is an actual nearest-neighbor pair. -/
theorem gridAdjacent_edge (e : IntegerGridExactness.Edge) :
    GridAdjacent e.1 (IntegerGridExactness.edgeHead e) := by
  obtain ⟨p,d⟩ := e
  fin_cases d
  · apply Or.inl
    exact ⟨rfl,by simp [IntegerGridExactness.edgeHead]⟩
  · apply Or.inr
    exact ⟨rfl,by simp [IntegerGridExactness.edgeHead]⟩

def vertexChain (p : IntegerGridExactness.Vertex) : LinkVertices g :=
  ⟨simplex [coordinateLine g p],by
    have h := simplex_mem_chains (link g) _ (singleton_allowed g h0 h1 h2 p)
    change simplex [coordinateLine g p] ∈ chains (link g) 1 at h
    exact h⟩

def edgeChain (e : IntegerGridExactness.Edge) : LinkEdges g :=
  ⟨simplex [coordinateLine g e.1,coordinateLine g (IntegerGridExactness.edgeHead e)],
    by
      have h := simplex_mem_chains (link g) _ (pair_allowed g h0 h1 h2 _ _ (gridAdjacent_edge e))
      change simplex [coordinateLine g e.1,coordinateLine g (IntegerGridExactness.edgeHead e)] ∈
        chains (link g) 2 at h
      exact h⟩

/-- The grid vertices map to their actual rational line vertices. -/
def vertexTransport : IntegerGridExactness.C₀ →ₗ[ℚ] LinkVertices g :=
  Finsupp.linearCombination ℚ (vertexChain g h0 h1 h2)

/-- Grid unit edges map to the actual ordered rational-line edge simplices. -/
def edgeTransport : IntegerGridExactness.C₁ →ₗ[ℚ] LinkEdges g :=
  Finsupp.linearCombination ℚ (edgeChain g h0 h1 h2)

@[simp] theorem vertexTransport_single (p : IntegerGridExactness.Vertex) (q : ℚ) :
    vertexTransport g h0 h1 h2 (Finsupp.single p q) = q • vertexChain g h0 h1 h2 p :=
  Finsupp.linearCombination_single ℚ q p

@[simp] theorem edgeTransport_single (e : IntegerGridExactness.Edge) (q : ℚ) :
    edgeTransport g h0 h1 h2 (Finsupp.single e q) = q • edgeChain g h0 h1 h2 e :=
  Finsupp.linearCombination_single ℚ q e

@[simp] theorem vertexTransport_vertex (p : IntegerGridExactness.Vertex) :
    vertexTransport g h0 h1 h2 (IntegerGridExactness.vertex p) = vertexChain g h0 h1 h2 p := by
  simp only [IntegerGridExactness.vertex,vertexTransport_single,one_smul]

theorem differential_edgeChain (e : IntegerGridExactness.Edge) :
    differential (link g) 1 (edgeChain g h0 h1 h2 e) =
      vertexChain g h0 h1 h2 (IntegerGridExactness.edgeHead e) - vertexChain g h0 h1 h2 e.1 := by
  apply Subtype.ext
  change boundary (simplex [coordinateLine g e.1,coordinateLine g (IntegerGridExactness.edgeHead e)]) = _
  simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex]
  rfl

/-- The actual grid and link endpoint boundaries commute with transport. -/
theorem differential_edgeTransport (c : IntegerGridExactness.C₁) :
    differential (link g) 1 (edgeTransport g h0 h1 h2 c) =
      vertexTransport g h0 h1 h2 (IntegerGridExactness.boundary₁ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single e q =>
    simp only [edgeTransport_single,map_smul,differential_edgeChain,
      IntegerGridExactness.boundary₁_single,map_sub,vertexTransport_vertex,smul_sub]

/-- Coordinate extraction is used only on the proved coordinate image. -/
def coordinate (L : RationalLine) : IntegerGridExactness.Vertex := by
  classical
  exact if h : ∃ p, coordinateLine g p = L then h.choose else (0,0)

@[simp] theorem coordinate_coordinateLine (p : IntegerGridExactness.Vertex) :
    coordinate g (coordinateLine g p) = p := by
  classical
  unfold coordinate
  rw [dite_eq_left ⟨p,rfl⟩]
  exact coordinateLine_injective g (Exists.choose_spec (⟨p,rfl⟩ : ∃ q, coordinateLine g q = coordinateLine g p))

def vertexValue : List RationalLine → IntegerGridExactness.C₀
  | [L] => IntegerGridExactness.vertex (coordinate g L)
  | _ => 0

theorem vertexValue_alternating : SpanChainComparison.AlternatingLists (vertexValue g) := by
  intro p a b s
  cases p with
  | nil => simp [vertexValue]
  | cons L p => cases p <;> simp [vertexValue]

def vertexCoordinates : LinkVertices g →ₗ[ℚ] IntegerGridExactness.C₀ :=
  (SpanChainComparison.evaluate (vertexValue g) (vertexValue_alternating g)).comp (chains (link g) 1).subtype

@[simp] theorem vertexCoordinates_vertexChain (p : IntegerGridExactness.Vertex) :
    vertexCoordinates g (vertexChain g h0 h1 h2 p) = IntegerGridExactness.vertex p := by
  change SpanChainComparison.evaluate (vertexValue g) (vertexValue_alternating g)
    (simplex [coordinateLine g p]) = _
  rw [SpanChainComparison.evaluate_simplex]
  change IntegerGridExactness.vertex (coordinate g (coordinateLine g p)) = _
  rw [coordinate_coordinateLine]

theorem vertexCoordinates_vertexTransport (z : IntegerGridExactness.C₀) :
    vertexCoordinates g (vertexTransport g h0 h1 h2 z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single p q =>
    rw [vertexTransport_single,map_smul,vertexCoordinates_vertexChain,
      IntegerGridExactness.vertex,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem vertexTransport_injective : Function.Injective (vertexTransport g h0 h1 h2) :=
  (show Function.LeftInverse (vertexCoordinates g) (vertexTransport g h0 h1 h2) from
    vertexCoordinates_vertexTransport g h0 h1 h2).injective

include h0 h1 in
private theorem exists_coordinates_of_allowed {l : List RationalLine}
    (hl : Allowed (link g) l) {L : RationalLine} (hL : L ∈ l) :
    ∃ p : IntegerGridExactness.Vertex, coordinateLine g p = L := by
  rcases hl with rfl | hl
  · simp at hL
  · apply exists_coordinates g h0 h1 L (hl.2 L (List.mem_toFinset.mpr hL))
    apply (ambient.isRelLowerSet_faces hl.1.2).2 ?_ (by simp)
    intro A hA
    simp only [Finset.mem_insert,Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (by simp [badEdge])
    · exact Finset.mem_union_left _ (by simp [badEdge])
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hL)

/-- Every nearest-neighbor pair is a positive unit edge or its reverse. -/
theorem gridAdjacent_oriented {p q : IntegerGridExactness.Vertex} (h : GridAdjacent p q) :
    ∃ e : IntegerGridExactness.Edge,
      (e.1 = p ∧ IntegerGridExactness.edgeHead e = q) ∨
      (e.1 = q ∧ IntegerGridExactness.edgeHead e = p) := by
  rcases h with ⟨hy,hd⟩ | ⟨hx,hd⟩
  · rcases Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr hd) with he | he
    · refine ⟨(q,0),Or.inr ⟨rfl,?_⟩⟩
      apply Prod.ext
      · change q.1+1 = p.1
        omega
      · exact hy.symm
    · refine ⟨(p,0),Or.inl ⟨rfl,?_⟩⟩
      apply Prod.ext
      · change p.1+1 = q.1
        omega
      · exact hy
  · rcases Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr hd) with he | he
    · refine ⟨(q,1),Or.inr ⟨rfl,?_⟩⟩
      apply Prod.ext
      · exact hx.symm
      · change q.2+1 = p.2
        omega
    · refine ⟨(p,1),Or.inl ⟨rfl,?_⟩⟩
      apply Prod.ext
      · exact hx
      · change p.2+1 = q.2
        omega

private theorem edge_simplex_mem_range (L M : RationalLine)
    (hl : Allowed (link g) [L,M]) (hc : simplex [L,M] ∈ LinkEdges g) :
    (⟨simplex [L,M],hc⟩ : LinkEdges g) ∈ (edgeTransport g h0 h1 h2).range := by
  obtain ⟨p,rfl⟩ := exists_coordinates_of_allowed g h0 h1 hl (by simp : L ∈ [L,M])
  obtain ⟨q,rfl⟩ := exists_coordinates_of_allowed g h0 h1 hl (by simp : M ∈ [coordinateLine g p,M])
  by_cases he : p = q
  · subst q
    have hz : (⟨simplex [coordinateLine g p,coordinateLine g p],hc⟩ : LinkEdges g) = 0 :=
      Subtype.ext (simplex_repeat_adjacent _ [])
    rw [hz]
    exact (edgeTransport g h0 h1 h2).range.zero_mem
  · have hadj : GridAdjacent p q := by
      apply gridAdjacent_of_face g p q he
      have hf := hl.resolve_left (by simp)
      obtain ⟨_,k,hk⟩ := hf.1.2
      refine ⟨by simp,k,?_⟩
      intro A hA
      apply hk
      simpa [badEdge,or_comm,or_left_comm,or_assoc] using hA
    obtain ⟨e,he⟩ := gridAdjacent_oriented hadj
    rcases he with ⟨hp,hq⟩ | ⟨hq,hp⟩
    · refine ⟨Finsupp.single e 1,?_⟩
      rw [edgeTransport_single,one_smul]
      apply Subtype.ext
      change simplex [coordinateLine g e.1,coordinateLine g (IntegerGridExactness.edgeHead e)] = _
      rw [hp,hq]
    · refine ⟨-Finsupp.single e 1,?_⟩
      rw [map_neg,edgeTransport_single,one_smul]
      apply Subtype.ext
      change -simplex [coordinateLine g e.1,coordinateLine g (IntegerGridExactness.edgeHead e)] = _
      rw [hq,hp]
      exact (simplex_swap_eq_neg _ _ []).symm

/-- Every actual oriented link edge has a finite grid-edge lift. -/
theorem edgeTransport_surjective : Function.Surjective (edgeTransport g h0 h1 h2) := by
  intro c
  suffices c ∈ (edgeTransport g h0 h1 h2).range from this
  obtain ⟨c,hc⟩ := c
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    exact edge_simplex_mem_range g h0 h1 h2 L M hl _
  | zero => exact (edgeTransport g h0 h1 h2).range.zero_mem
  | add x y hx hy ihx ihy => exact (edgeTransport g h0 h1 h2).range.add_mem ihx ihy
  | smul q x hx ih => exact (edgeTransport g h0 h1 h2).range.smul_mem q ih

/-- A unit square gives its actual four-edge loop in the link. -/
def squareLoop (p : IntegerGridExactness.Vertex) : LinkEdges g :=
  edgeTransport g h0 h1 h2 (IntegerGridExactness.squareBoundary p)

/-- The transported square has the literal four ordered edge simplices. -/
theorem squareLoop_val (p : IntegerGridExactness.Vertex) :
    (squareLoop g h0 h1 h2 p).val =
      simplex [coordinateLine g p,coordinateLine g (p.1+1,p.2)] +
      simplex [coordinateLine g (p.1+1,p.2),coordinateLine g (p.1+1,p.2+1)] -
      simplex [coordinateLine g (p.1,p.2+1),coordinateLine g (p.1+1,p.2+1)] -
      simplex [coordinateLine g p,coordinateLine g (p.1,p.2+1)] := by
  change (edgeTransport g h0 h1 h2 (IntegerGridExactness.horizontal p +
    IntegerGridExactness.vertical (p.1+1,p.2) - IntegerGridExactness.horizontal (p.1,p.2+1) -
    IntegerGridExactness.vertical p)).val = _
  rw [map_sub,map_sub,map_add]
  simp only [IntegerGridExactness.horizontal,IntegerGridExactness.vertical,
    edgeTransport_single,one_smul]
  rfl

/-- Finite square combinations are transported as loops, not as simplicial two-chains. -/
def squareTransport : IntegerGridExactness.C₂ →ₗ[ℚ] LinkEdges g :=
  (edgeTransport g h0 h1 h2).comp IntegerGridExactness.boundary₂

@[simp] theorem squareTransport_square (p : IntegerGridExactness.Vertex) :
    squareTransport g h0 h1 h2 (IntegerGridExactness.square p) = squareLoop g h0 h1 h2 p := by
  change edgeTransport g h0 h1 h2 (IntegerGridExactness.boundary₂ (IntegerGridExactness.square p)) = _
  rw [IntegerGridExactness.boundary₂_square]
  rfl

theorem squareLoop_boundary (p : IntegerGridExactness.Vertex) :
    differential (link g) 1 (squareLoop g h0 h1 h2 p) = 0 := by
  rw [squareLoop,differential_edgeTransport,IntegerGridExactness.boundary₁_squareBoundary,map_zero]

/-- Every finite oriented link cycle is a finite rational sum of actual square loops. -/
theorem cycle_generated_by_squares (c : LinkEdges g) (hc : differential (link g) 1 c = 0) :
    ∃ z : IntegerGridExactness.C₂,
      c = edgeTransport g h0 h1 h2 (IntegerGridExactness.boundary₂ z) := by
  obtain ⟨x,rfl⟩ := edgeTransport_surjective g h0 h1 h2 c
  have hx : IntegerGridExactness.boundary₁ x = 0 := by
    apply vertexTransport_injective g h0 h1 h2
    rw [← differential_edgeTransport,hc,map_zero]
  have hm : x ∈ IntegerGridExactness.boundary₂.range := by
    rw [← IntegerGridExactness.ker_boundary₁_eq_range_boundary₂]
    exact hx
  obtain ⟨z,hz⟩ := hm
  exact ⟨z,congrArg (edgeTransport g h0 h1 h2) hz.symm⟩

/-- The same actual square-loop generation statement for raw supported oriented cycles. -/
theorem supported_cycle_generated_by_squares {c : Chain RationalLine}
    (hc : c ∈ chains (link g) 2) (hz : boundary c = 0) :
    ∃ z : IntegerGridExactness.C₂,
      c = (edgeTransport g h0 h1 h2 (IntegerGridExactness.boundary₂ z)).val := by
  obtain ⟨z,he⟩ := cycle_generated_by_squares g h0 h1 h2 ⟨c,hc⟩ (Subtype.ext hz)
  exact ⟨z,congrArg Subtype.val he⟩

end TernaryPoly.BadEdgeLinkChains
