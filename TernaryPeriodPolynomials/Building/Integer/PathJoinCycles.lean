module

public import TernaryPeriodPolynomials.Building.Integer.Exactness
public import TernaryPeriodPolynomials.Building.Span.ChainComparison
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainMap

@[expose] public section


noncomputable section
namespace TernaryPoly.IntegerPathJoinCycles
open OrientedListChains SpanChainComparison
abbrev Vertex := ℤ ⊕ ℤ
abbrev C := Chain Vertex

def left (k : ℤ) : Vertex := .inl k
def right (k : ℤ) : Vertex := .inr k

/-- An oriented mixed triangle for each horizontal/vertical parameter edge. -/
def triangle (e : IntegerGridExactness.Edge) : C :=
  if e.2 = 0 then simplex [left e.1.1,left (e.1.1+1),right e.1.2]
  else -simplex [left e.1.1,right e.1.2,right (e.1.2+1)]

def mixed : IntegerGridExactness.C₁ →ₗ[ℚ] Chain Vertex :=
  Finsupp.linearCombination ℚ triangle

/-- The oriented cross-edge coefficient, ignoring the two individual path edges. -/
def crossValue : List Vertex → IntegerGridExactness.C₀
  | [.inl k,.inr l] => Finsupp.single (k,l) 1
  | [.inr l,.inl k] => -Finsupp.single (k,l) 1
  | _ => 0

theorem crossValue_alternating : AlternatingLists crossValue := by
  intro p a b s
  cases p with
  | nil =>
    cases s with
    | nil => cases a <;> cases b <;> simp [crossValue]
    | cons c s => cases a <;> cases b <;> simp [crossValue]
  | cons c p =>
    cases p with
    | nil => cases c <;> cases a <;> simp [crossValue]
    | cons d p => cases c <;> cases d <;> simp [crossValue]

def cross : C →ₗ[ℚ] IntegerGridExactness.C₀ := evaluate crossValue crossValue_alternating

@[simp] theorem cross_simplex (l : List Vertex) : cross (simplex l) = crossValue l :=
  evaluate_simplex crossValue crossValue_alternating l

/-- Cross-edge boundary is the actual square-grid divergence of the triangle coefficients. -/
theorem cross_boundary_triangle (e : IntegerGridExactness.Edge) :
    cross (boundary (triangle e)) =
      IntegerGridExactness.vertex (IntegerGridExactness.edgeHead e) -
        IntegerGridExactness.vertex e.1 := by
  obtain ⟨⟨k,l⟩,j⟩ := e
  fin_cases j <;> simp [triangle,IntegerGridExactness.edgeHead,boundary_cons,
    boundary_nil,cons_simplex,crossValue,left,right,IntegerGridExactness.vertex]

/-- Boundary compatibility holds for every finite mixed triangle chain. -/
theorem cross_boundary_mixed (z : IntegerGridExactness.C₁) :
    cross (boundary (mixed z)) = IntegerGridExactness.boundary₁ z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | single e q =>
    rw [mixed,Finsupp.linearCombination_single,map_smul,map_smul,cross_boundary_triangle,
      IntegerGridExactness.boundary₁_single]

/-- The join of two adjacent path edges, with the orientation matching grid divergence. -/
def tetrahedron (p : IntegerGridExactness.Vertex) : C :=
  -simplex [left p.1,left (p.1+1),right p.2,right (p.2+1)]

def filling : IntegerGridExactness.C₂ →ₗ[ℚ] C := Finsupp.linearCombination ℚ tetrahedron

/-- Every parameter square yields precisely one tetrahedral sphere of the path join. -/
theorem mixed_squareBoundary (p : IntegerGridExactness.Vertex) :
    mixed (IntegerGridExactness.squareBoundary p) = boundary (tetrahedron p) := by
  simp only [IntegerGridExactness.squareBoundary,map_sub,map_add,
    IntegerGridExactness.horizontal,IntegerGridExactness.vertical,mixed,
    Finsupp.linearCombination_single,one_smul]
  simp only [triangle,ite_true,show (1 : Fin 2) ≠ 0 from by decide,ite_false,
    tetrahedron,map_neg,boundary_cons,boundary_nil,map_zero,map_sub,cons_simplex]
  abel

/-- Exact chain compatibility extends the square/tetrahedron identity to arbitrary finite sums. -/
theorem mixed_boundary₂ (z : IntegerGridExactness.C₂) :
    mixed (IntegerGridExactness.boundary₂ z) = boundary (filling z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | single p q =>
    rw [IntegerGridExactness.boundary₂_single,map_smul,mixed_squareBoundary,
      filling,Finsupp.linearCombination_single,map_smul]

/-- Vanishing of just the cross-edge divergence suffices; individual path-edge terms need
not be assumed zero beforehand. -/
theorem mixed_eq_boundary_of_cross_zero {z : IntegerGridExactness.C₁}
    (hz : cross (boundary (mixed z)) = 0) :
    ∃ a : IntegerGridExactness.C₂, mixed z = boundary (filling a) := by
  have hd : IntegerGridExactness.boundary₁ z = 0 := by rwa [cross_boundary_mixed] at hz
  have hk : z ∈ LinearMap.ker IntegerGridExactness.boundary₁ := hd
  rw [IntegerGridExactness.ker_boundary₁_eq_range_boundary₂] at hk
  obtain ⟨a,ha⟩ := hk
  exact ⟨a,by rw [← ha,mixed_boundary₂]⟩

/-- Every finite mixed-triangle cycle is a finite sum of actual tetrahedral square spheres. -/
theorem mixed_cycle_eq_boundary {z : IntegerGridExactness.C₁} (hz : boundary (mixed z) = 0) :
    ∃ a : IntegerGridExactness.C₂, mixed z = boundary (filling a) := by
  exact mixed_eq_boundary_of_cross_zero (by rw [hz,map_zero])

/-- The explicit generator-span version requires no choice of a basis of the oriented quotient. -/
theorem mixed_span_cycle_eq_boundary {c : C}
    (hc : c ∈ Submodule.span ℚ (Set.range triangle)) (hd : boundary c = 0) :
    ∃ a : IntegerGridExactness.C₂, c = boundary (filling a) := by
  have hr : c ∈ LinearMap.range mixed := by
    rwa [mixed,Finsupp.range_linearCombination]
  obtain ⟨z,rfl⟩ := hr
  exact mixed_cycle_eq_boundary hd

/-- Finite square-sphere caps can be assembled after any actual vertex relabeling. -/
theorem mapped_mixed_filling {W : Type*} (f : Vertex → W) (D : Submodule ℚ (Chain W))
    (hcaps : ∀ p : IntegerGridExactness.Vertex, ∃ t : Chain W, t ∈ D ∧
      boundary t = OrientedChainMap.map f (boundary (tetrahedron p)))
    {z : IntegerGridExactness.C₁} (hz : cross (boundary (mixed z)) = 0) :
    ∃ t : Chain W, t ∈ D ∧ boundary t = OrientedChainMap.map f (mixed z) := by
  obtain ⟨a,ha⟩ := mixed_eq_boundary_of_cross_zero hz
  have hfinite (a : IntegerGridExactness.C₂) : ∃ t : Chain W, t ∈ D ∧
      boundary t = OrientedChainMap.map f (boundary (filling a)) := by
    induction a using Finsupp.induction_linear with
    | zero => exact ⟨0,D.zero_mem,by simp⟩
    | add a b ha hb =>
      obtain ⟨t,ht,hdt⟩ := ha
      obtain ⟨u,hu,hdu⟩ := hb
      exact ⟨t+u,D.add_mem ht hu,by simp only [map_add,hdt,hdu]⟩
    | single p q =>
      obtain ⟨t,ht,hdt⟩ := hcaps p
      refine ⟨q • t,D.smul_mem q ht,?_⟩
      simp only [filling,Finsupp.linearCombination_single,map_smul,hdt]
  obtain ⟨t,ht,hdt⟩ := hfinite a
  exact ⟨t,ht,by rw [ha]; exact hdt⟩

/-- An injective actual relabeling detects the model cycle condition needed for the cap assembly. -/
theorem mapped_mixed_cycle_filling {W : Type*} (f : Vertex → W) (hf : Function.Injective f)
    (D : Submodule ℚ (Chain W))
    (hcaps : ∀ p : IntegerGridExactness.Vertex, ∃ t : Chain W, t ∈ D ∧
      boundary t = OrientedChainMap.map f (boundary (tetrahedron p)))
    {z : IntegerGridExactness.C₁} (hz : boundary (OrientedChainMap.map f (mixed z)) = 0) :
    ∃ t : Chain W, t ∈ D ∧ boundary t = OrientedChainMap.map f (mixed z) := by
  rw [OrientedChainMap.boundary_map] at hz
  have he := (OrientedChainMap.map_eq_zero_iff f hf (boundary (mixed z))).mp hz
  exact mapped_mixed_filling f D hcaps (by rw [he,map_zero])

end TernaryPoly.IntegerPathJoinCycles
