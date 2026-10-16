module

public import TernaryPeriodPolynomials.Building.Integer.PathExactness
public import TernaryPeriodPolynomials.Building.Span.ChainComparison

@[expose] public section


/-! Explicit transport between integer finite-support path chains and actual
oriented-list chains. No Farey or lattice identification is asserted. -/

noncomputable section
namespace TernaryPoly.IntegerPathChains
open OrientedListChains

/-- The actual integer-path faces: nonempty subsets of one neighboring pair. -/
def pathComplex : PreAbstractSimplicialComplex ℤ where
  faces := {s | s.Nonempty ∧ ∃ n : ℤ, s ⊆ {n,n+1}}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    obtain ⟨n,hn⟩ := hs.2
    exact ⟨ht,n,hts.trans hn⟩

abbrev Vertices := chains pathComplex 1
abbrev Edges := chains pathComplex 2

def vertexChain (n : ℤ) : Vertices :=
  ⟨simplex [n],simplex_mem_chains pathComplex [n] (Or.inr (by
    refine ⟨by simp,n,?_⟩
    intro m hm
    simp only [List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,
      Finset.mem_singleton] at hm ⊢
    exact Or.inl (by simpa using hm)))⟩

def edgeChain (n : ℤ) : Edges :=
  ⟨simplex [n,n+1],simplex_mem_chains pathComplex [n,n+1] (Or.inr (by
    refine ⟨by simp,n,?_⟩
    intro m hm
    simpa using hm))⟩

/-- Actual endpoint transport. -/
def vertexTransport : IntegerPathExactness.C₀ →ₗ[ℚ] Vertices :=
  Finsupp.linearCombination ℚ vertexChain

/-- Actual positively oriented neighboring-edge transport. -/
def edgeTransport : IntegerPathExactness.C₁ →ₗ[ℚ] Edges :=
  Finsupp.linearCombination ℚ edgeChain

@[simp] theorem vertexTransport_single (n : ℤ) (q : ℚ) :
    vertexTransport (Finsupp.single n q) = q • vertexChain n :=
  Finsupp.linearCombination_single ℚ q n

@[simp] theorem edgeTransport_single (n : ℤ) (q : ℚ) :
    edgeTransport (Finsupp.single n q) = q • edgeChain n :=
  Finsupp.linearCombination_single ℚ q n

@[simp] theorem vertexTransport_vertex (n : ℤ) :
    vertexTransport (IntegerPathExactness.vertex n) = vertexChain n := by
  simp only [IntegerPathExactness.vertex,vertexTransport_single,one_smul]

@[simp] theorem edgeTransport_edge (n : ℤ) :
    edgeTransport (IntegerPathExactness.edge n) = edgeChain n := by
  simp only [IntegerPathExactness.edge,edgeTransport_single,one_smul]

/-- The literal integer endpoints agree under oriented boundary. -/
theorem differential_edgeChain (n : ℤ) :
    differential pathComplex 1 (edgeChain n) = vertexChain (n+1) - vertexChain n := by
  apply Subtype.ext
  change boundary (simplex [n,n+1]) = simplex [n+1] - simplex [n]
  simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex]

/-- Boundary commutes with both actual chain transports. -/
theorem differential_edgeTransport (c : IntegerPathExactness.C₁) :
    differential pathComplex 1 (edgeTransport c) =
      vertexTransport (IntegerPathExactness.boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single n q =>
    simp only [edgeTransport_single,map_smul,differential_edgeChain,
      IntegerPathExactness.boundary_single,map_sub,vertexTransport_vertex,smul_sub]

/-- Reading one-vertex coefficients uses an actual map from the alternating quotient. -/
def vertexValue : List ℤ → IntegerPathExactness.C₀
  | [n] => IntegerPathExactness.vertex n
  | _ => 0

theorem vertexValue_alternating : SpanChainComparison.AlternatingLists vertexValue := by
  intro p a b s
  cases p with
  | nil => simp [vertexValue]
  | cons n p => cases p <;> simp [vertexValue]

def vertexCoordinates : Vertices →ₗ[ℚ] IntegerPathExactness.C₀ :=
  (SpanChainComparison.evaluate vertexValue vertexValue_alternating).comp (chains pathComplex 1).subtype

@[simp] theorem vertexCoordinates_vertexChain (n : ℤ) :
    vertexCoordinates (vertexChain n) = IntegerPathExactness.vertex n := by
  change SpanChainComparison.evaluate vertexValue vertexValue_alternating (simplex [n]) = _
  rw [SpanChainComparison.evaluate_simplex]
  rfl

theorem vertexCoordinates_vertexTransport (z : IntegerPathExactness.C₀) :
    vertexCoordinates (vertexTransport z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single n q =>
    rw [vertexTransport_single,map_smul,vertexCoordinates_vertexChain,
      IntegerPathExactness.vertex,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem vertexTransport_vertexCoordinates (z : Vertices) :
    vertexTransport (vertexCoordinates z) = z := by
  obtain ⟨z,hz⟩ := z
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l,hlen,hl,rfl⟩ := hz
    obtain ⟨n,rfl⟩ := List.length_eq_one_iff.mp hlen
    change vertexTransport (vertexCoordinates (vertexChain n)) = vertexChain n
    rw [vertexCoordinates_vertexChain,vertexTransport_vertex]
  | zero => exact map_zero (vertexTransport.comp vertexCoordinates)
  | add x y hx hy ihx ihy =>
    change vertexTransport (vertexCoordinates ((⟨x,hx⟩ : Vertices) + ⟨y,hy⟩)) =
      (⟨x,hx⟩ : Vertices) + ⟨y,hy⟩
    rw [map_add,map_add,ihx,ihy]
  | smul q x hx ih =>
    change vertexTransport (vertexCoordinates (q • (⟨x,hx⟩ : Vertices))) =
      q • (⟨x,hx⟩ : Vertices)
    rw [map_smul,map_smul,ih]

/-- The endpoint transport is an actual linear equivalence, with the displayed coefficient inverse. -/
def vertexEquiv : IntegerPathExactness.C₀ ≃ₗ[ℚ] Vertices :=
  { vertexTransport with
    invFun := vertexCoordinates
    left_inv := vertexCoordinates_vertexTransport
    right_inv := vertexTransport_vertexCoordinates }

/-- Coordinates of an oriented edge chain are recovered from its endpoints and signed paths. -/
def edgeCoordinates : Edges →ₗ[ℚ] IntegerPathExactness.C₁ :=
  IntegerPathExactness.pathLinear.comp (vertexCoordinates.comp (differential pathComplex 1))

theorem edgeCoordinates_edgeTransport (c : IntegerPathExactness.C₁) :
    edgeCoordinates (edgeTransport c) = c := by
  change IntegerPathExactness.pathLinear
    (vertexCoordinates (differential pathComplex 1 (edgeTransport c))) = c
  rw [differential_edgeTransport,vertexCoordinates_vertexTransport,
    IntegerPathExactness.pathLinear_boundary]

private theorem edge_simplex_mem_range (a b : ℤ) (hl : Allowed pathComplex [a,b])
    (hc : simplex [a,b] ∈ Edges) :
    (⟨simplex [a,b],hc⟩ : Edges) ∈ edgeTransport.range := by
  classical
  have he : @List.toFinset ℤ (Classical.decEq ℤ) [a,b] = [a,b].toFinset := by
    ext x
    simp only [List.mem_toFinset]
  have hf : [a,b].toFinset ∈ pathComplex := he ▸ hl.resolve_left (by simp)
  obtain ⟨n,hn⟩ := hf.2
  have ha : a = n ∨ a = n+1 := by simpa using hn (by simp : a ∈ [a,b].toFinset)
  have hb : b = n ∨ b = n+1 := by simpa using hn (by simp : b ∈ [a,b].toFinset)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp only [ha,hb] at hc ⊢
  · have he : (⟨simplex [n,n],hc⟩ : Edges) = 0 := Subtype.ext (simplex_repeat_adjacent n [])
    rw [he]
    exact edgeTransport.range.zero_mem
  · exact ⟨IntegerPathExactness.edge n,edgeTransport_edge n⟩
  · refine ⟨-IntegerPathExactness.edge n,?_⟩
    rw [map_neg,edgeTransport_edge]
    apply Subtype.ext
    exact (simplex_swap_eq_neg (n+1) n []).symm
  · have he : (⟨simplex [n+1,n+1],hc⟩ : Edges) = 0 :=
      Subtype.ext (simplex_repeat_adjacent (n+1) [])
    rw [he]
    exact edgeTransport.range.zero_mem

/-- The actual path faces give no additional edge generators beyond the neighboring pairs. -/
theorem edgeTransport_surjective : Function.Surjective edgeTransport := by
  intro c
  suffices c ∈ edgeTransport.range from this
  obtain ⟨c,hc⟩ := c
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
    exact edge_simplex_mem_range a b hl _
  | zero => exact edgeTransport.range.zero_mem
  | add x y hx hy ihx ihy => exact edgeTransport.range.add_mem ihx ihy
  | smul q x hx ih => exact edgeTransport.range.smul_mem q ih

theorem edgeTransport_edgeCoordinates (c : Edges) : edgeTransport (edgeCoordinates c) = c := by
  obtain ⟨z,rfl⟩ := edgeTransport_surjective c
  rw [edgeCoordinates_edgeTransport]

/-- The neighboring-edge transport is an actual linear equivalence. -/
def edgeEquiv : IntegerPathExactness.C₁ ≃ₗ[ℚ] Edges :=
  { edgeTransport with
    invFun := edgeCoordinates
    left_inv := edgeCoordinates_edgeTransport
    right_inv := edgeTransport_edgeCoordinates }

def augmentation : Vertices →ₗ[ℚ] ℚ := IntegerPathExactness.augmentation.comp vertexCoordinates

/-- Explicit finite fillers in the actual oriented path-chain model. -/
def pathFilling : Vertices →ₗ[ℚ] Edges :=
  edgeTransport.comp (IntegerPathExactness.pathLinear.comp vertexCoordinates)

theorem differential_pathFilling (z : Vertices) :
    differential pathComplex 1 (pathFilling z) = z - augmentation z • vertexChain 0 := by
  change differential pathComplex 1 (edgeTransport (IntegerPathExactness.pathLinear
    (vertexCoordinates z))) = _
  rw [differential_edgeTransport,IntegerPathExactness.boundary_pathLinear,map_sub,
    map_smul,vertexTransport_vertexCoordinates,vertexTransport_vertex]
  rfl

theorem pathFilling_differential (c : Edges) :
    pathFilling (differential pathComplex 1 c) = c := by
  obtain ⟨z,rfl⟩ := edgeTransport_surjective c
  change edgeTransport (IntegerPathExactness.pathLinear
    (vertexCoordinates (differential pathComplex 1 (edgeTransport z)))) = _
  rw [differential_edgeTransport,vertexCoordinates_vertexTransport,
    IntegerPathExactness.pathLinear_boundary]

/-- There are no finite oriented one-cycles in the actual infinite path complex. -/
theorem differential_injective : Function.Injective (differential pathComplex 1) :=
  (show Function.LeftInverse pathFilling (differential pathComplex 1) from
    pathFilling_differential).injective

theorem augmentation_differential (c : Edges) : augmentation (differential pathComplex 1 c) = 0 := by
  obtain ⟨z,rfl⟩ := edgeTransport_surjective c
  change IntegerPathExactness.augmentation
    (vertexCoordinates (differential pathComplex 1 (edgeTransport z))) = 0
  rw [differential_edgeTransport,vertexCoordinates_vertexTransport,
    IntegerPathExactness.augmentation_boundary]

/-- Finite reduced degree-zero exactness holds in the actual oriented path complex. -/
theorem ker_augmentation_eq_range_differential :
    LinearMap.ker augmentation = (differential pathComplex 1).range := by
  ext z
  constructor
  · intro hz
    refine ⟨pathFilling z,?_⟩
    rw [differential_pathFilling,LinearMap.mem_ker.mp hz,zero_smul,sub_zero]
  · rintro ⟨c,rfl⟩
    exact augmentation_differential c

end TernaryPoly.IntegerPathChains
