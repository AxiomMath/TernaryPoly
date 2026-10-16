module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Incidence
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.IncidencePaths
public import TernaryPeriodPolynomials.Building.Good.ChainComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryIncidenceChains
open OrdinaryIncidence
open TernaryPeriodPolynomial.PathCocycle

abbrev Edge := BipartitePathChains.Edge incidence
abbrev EdgeChains := BipartitePathChains.Chain₁ incidence
abbrev VertexChains := BipartitePathChains.Chain₀ Line Plane
abbrev boundary : EdgeChains →ₗ[ℚ] VertexChains := BipartitePathChains.boundary incidence

def edgeAction (g : GoodBuilding.K) : Equiv.Perm Edge :=
  BipartitePathChains.edgeEquiv (lineAction g) (planeAction g)
    (fun L P => (incidence_action_iff g L P).symm)
def edgeLinear (g : GoodBuilding.K) : EdgeChains ≃ₗ[ℚ] EdgeChains :=
  BipartitePathChains.chainEquiv (lineAction g) (planeAction g)
    (fun L P => (incidence_action_iff g L P).symm)
def vertexLinear (g : GoodBuilding.K) : VertexChains ≃ₗ[ℚ] VertexChains :=
  BipartitePathChains.vertexChainEquiv (lineAction g) (planeAction g)

@[simp] theorem edgeLinear_single (g : GoodBuilding.K) (e : Edge) (q : ℚ) :
    edgeLinear g (Finsupp.single e q) = Finsupp.single (edgeAction g e) q :=
  BipartitePathChains.chainEquiv_single _ _ _ _ _
@[simp] theorem vertexLinear_single (g : GoodBuilding.K) (v : Vertex) (q : ℚ) :
    vertexLinear g (Finsupp.single v q) = Finsupp.single (vertexAction g v) q :=
  BipartitePathChains.vertexChainEquiv_single _ _ _ _

theorem edgeAction_one (e : Edge) : edgeAction 1 e = e := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> exact ModThreeGoodAction.act_one _
theorem edgeAction_mul (g h : GoodBuilding.K) (e : Edge) :
    edgeAction (g*h) e = edgeAction g (edgeAction h e) := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> exact ModThreeGoodAction.act_mul g h _

def edgeRepresentation : Representation ℚ GoodBuilding.K EdgeChains where
  toFun g := (edgeLinear g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro c
    change edgeLinear 1 c = c
    induction c using Finsupp.induction_linear with
    | zero => exact map_zero _
    | add c d hc hd => rw [map_add,hc,hd]
    | single e q => rw [edgeLinear_single,edgeAction_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    change edgeLinear (g*h) c = edgeLinear g (edgeLinear h c)
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add c d hc hd => simp only [map_add,hc,hd]
    | single e q => simp only [edgeLinear_single,edgeAction_mul]

def vertexRepresentation : Representation ℚ GoodBuilding.K VertexChains where
  toFun g := (vertexLinear g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro c
    change vertexLinear 1 c = c
    induction c using Finsupp.induction_linear with
    | zero => exact map_zero _
    | add c d hc hd => rw [map_add,hc,hd]
    | single v q => rw [vertexLinear_single,vertexAction_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    change vertexLinear (g*h) c = vertexLinear g (vertexLinear h c)
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add c d hc hd => simp only [map_add,hc,hd]
    | single v q => simp only [vertexLinear_single,vertexAction_mul]

@[simp] theorem edgeRepresentation_single (g : GoodBuilding.K) (e : Edge) (q : ℚ) :
    edgeRepresentation g (Finsupp.single e q) = Finsupp.single (edgeAction g e) q := edgeLinear_single g e q
@[simp] theorem vertexRepresentation_single (g : GoodBuilding.K) (v : Vertex) (q : ℚ) :
    vertexRepresentation g (Finsupp.single v q) = Finsupp.single (vertexAction g v) q := vertexLinear_single g v q

theorem boundary_equivariant (g : GoodBuilding.K) (c : EdgeChains) :
    boundary (edgeRepresentation g c) = vertexRepresentation g (boundary c) :=
  BipartitePathChains.boundary_chainEquiv (lineAction g) (planeAction g)
    (fun L P => (incidence_action_iff g L P).symm) c

/-- The actual ordinary incidence boundary complex, with its genuine K action. -/
def complex : BoundaryData GoodBuilding.K EdgeChains VertexChains where
  chains := edgeRepresentation
  vertices := vertexRepresentation
  boundary := boundary
  equivariant := boundary_equivariant
abbrev Cycles := complex.Cycles

/-- Literal inclusion of Good incidence flags in the ordinary flag set. -/
def goodEdge (e : GoodChainComplex.GoodEdge) : Edge :=
  ⟨(goodLine e.val.1,goodPlane e.val.2),e.property⟩
theorem goodEdge_injective : Function.Injective goodEdge := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact goodLine_injective (congrArg (fun e : Edge => e.val.1) h)
  · exact goodPlane_injective (congrArg (fun e : Edge => e.val.2) h)

def edgeInclusion : GoodChainComplex.EdgeChains →ₗ[ℚ] EdgeChains :=
  Finsupp.lmapDomain ℚ ℚ goodEdge
def vertexInclusion : GoodChainComplex.VertexChains →ₗ[ℚ] VertexChains :=
  Finsupp.lmapDomain ℚ ℚ goodVertex

@[simp] theorem edgeInclusion_single (e : GoodChainComplex.GoodEdge) (q : ℚ) :
    edgeInclusion (Finsupp.single e q) = Finsupp.single (goodEdge e) q := Finsupp.mapDomain_single
@[simp] theorem vertexInclusion_single (v : GoodBuilding.GoodVertex) (q : ℚ) :
    vertexInclusion (Finsupp.single v q) = Finsupp.single (goodVertex v) q := Finsupp.mapDomain_single

theorem edgeInclusion_injective : Function.Injective edgeInclusion :=
  Finsupp.mapDomain_injective goodEdge_injective
theorem vertexInclusion_injective : Function.Injective vertexInclusion :=
  Finsupp.mapDomain_injective goodVertex_injective

theorem boundary_inclusion (c : GoodChainComplex.EdgeChains) :
    boundary (edgeInclusion c) = vertexInclusion (GoodChainComplex.boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single e q =>
    change boundary (edgeInclusion (Finsupp.single e q)) =
      vertexInclusion (BipartitePathChains.boundary GoodChainComplex.incidence (Finsupp.single e q))
    simp only [edgeInclusion_single,BipartitePathChains.boundary_single,map_sub,vertexInclusion_single]
    rfl

theorem goodEdge_equivariant (g : GoodBuilding.K) (e : GoodChainComplex.GoodEdge) :
    goodEdge (GoodChainComplex.edgeAction g e) = edgeAction g (goodEdge e) := rfl

theorem edgeInclusion_equivariant (g : GoodBuilding.K) (c : GoodChainComplex.EdgeChains) :
    edgeInclusion (GoodChainComplex.edgeRepresentation g c) = edgeRepresentation g (edgeInclusion c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single e q => simp only [GoodChainComplex.edgeRepresentation_single,edgeInclusion_single,
      edgeRepresentation_single,goodEdge_equivariant]

theorem vertexInclusion_equivariant (g : GoodBuilding.K) (c : GoodChainComplex.VertexChains) :
    vertexInclusion (GoodChainComplex.vertexRepresentation g c) = vertexRepresentation g (vertexInclusion c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single v q => simp only [GoodChainComplex.vertexRepresentation_single,vertexInclusion_single,
      vertexRepresentation_single,goodVertex_equivariant]

/-- The actual inclusion of Good cycles into ordinary cycles. -/
def cycleInclusion : GoodChainComplex.Cycles →ₗ[ℚ] Cycles :=
  (edgeInclusion.comp GoodChainComplex.complex.Cycles.subtype).codRestrict _ (fun c => by
    change boundary (edgeInclusion c.val) = 0
    rw [boundary_inclusion,show GoodChainComplex.boundary c.val = 0 from c.property,map_zero])

@[simp] theorem cycleInclusion_coe (c : GoodChainComplex.Cycles) :
    (cycleInclusion c).val = edgeInclusion c.val := rfl

theorem cycleInclusion_injective : Function.Injective cycleInclusion := by
  intro c d h
  exact Subtype.ext (edgeInclusion_injective (congrArg Subtype.val h))

theorem cycleInclusion_equivariant (g : GoodBuilding.K) (c : GoodChainComplex.Cycles) :
    cycleInclusion (GoodChainComplex.complex.cyclesAction g c) = complex.cyclesAction g (cycleInclusion c) := by
  apply Subtype.ext
  exact edgeInclusion_equivariant g c.val

theorem augmentation_inclusion (c : GoodChainComplex.VertexChains) :
    OrdinaryIncidencePaths.augmentation (vertexInclusion c) = OrdinaryIncidencePaths.augmentation c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single v q => simp only [vertexInclusion_single,OrdinaryIncidencePaths.augmentation_single]

end TernaryPoly.OrdinaryIncidenceChains
