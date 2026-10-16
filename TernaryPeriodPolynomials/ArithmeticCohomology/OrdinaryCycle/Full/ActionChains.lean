module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.Action

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFullAction
open OrdinaryIncidenceChains OrdinaryIncidence
open TernaryPeriodPolynomial.PathCocycle

def edgeAction (g : GL3) : Equiv.Perm Edge :=
  BipartitePathChains.edgeEquiv (lineAction g) (planeAction g)
    (fun L P => (incidence_action_iff g L P).symm)
def edgeLinear (g : GL3) : EdgeChains ≃ₗ[ℚ] EdgeChains :=
  BipartitePathChains.chainEquiv (lineAction g) (planeAction g)
    (fun L P => (incidence_action_iff g L P).symm)
def vertexLinear (g : GL3) : VertexChains ≃ₗ[ℚ] VertexChains :=
  BipartitePathChains.vertexChainEquiv (lineAction g) (planeAction g)

@[simp] theorem edgeLinear_single (g : GL3) (e : Edge) (q : ℚ) :
    edgeLinear g (Finsupp.single e q) = Finsupp.single (edgeAction g e) q :=
  BipartitePathChains.chainEquiv_single _ _ _ _ _
@[simp] theorem vertexLinear_single (g : GL3) (v : Vertex) (q : ℚ) :
    vertexLinear g (Finsupp.single v q) = Finsupp.single (vertexAction g v) q :=
  BipartitePathChains.vertexChainEquiv_single _ _ _ _

theorem edgeAction_one (e : Edge) : edgeAction 1 e = e := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> exact subspaceAction_one _
theorem edgeAction_mul (g h : GL3) (e : Edge) :
    edgeAction (g*h) e = edgeAction g (edgeAction h e) := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> exact subspaceAction_mul g h _

def edgeRepresentation : Representation ℚ GL3 EdgeChains where
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

def vertexRepresentation : Representation ℚ GL3 VertexChains where
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

@[simp] theorem edgeRepresentation_single (g : GL3) (e : Edge) (q : ℚ) :
    edgeRepresentation g (Finsupp.single e q) = Finsupp.single (edgeAction g e) q := edgeLinear_single g e q
@[simp] theorem vertexRepresentation_single (g : GL3) (v : Vertex) (q : ℚ) :
    vertexRepresentation g (Finsupp.single v q) = Finsupp.single (vertexAction g v) q := vertexLinear_single g v q

theorem boundary_equivariant (g : GL3) (c : EdgeChains) :
    boundary (edgeRepresentation g c) = vertexRepresentation g (boundary c) :=
  BipartitePathChains.boundary_chainEquiv (lineAction g) (planeAction g)
    (fun L P => (incidence_action_iff g L P).symm) c

/-- The actual ordinary incidence boundary complex, with its genuine rational GL3 action. -/
def complex : BoundaryData GL3 EdgeChains VertexChains where
  chains := edgeRepresentation
  vertices := vertexRepresentation
  boundary := boundary
  equivariant := boundary_equivariant



/-- The extension acts on the existing literal cycle kernel. -/
def cycleAction : Representation ℚ GL3 OrdinaryIncidenceChains.Cycles := complex.cyclesAction

@[simp] theorem edgeRepresentation_K (g : GoodBuilding.K) (c : EdgeChains) :
    edgeRepresentation (integral g.val) c = OrdinaryIncidenceChains.edgeRepresentation g c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single e q =>
      rw [edgeRepresentation_single,OrdinaryIncidenceChains.edgeRepresentation_single]
      congr 1
@[simp] theorem vertexRepresentation_K (g : GoodBuilding.K) (c : VertexChains) :
    vertexRepresentation (integral g.val) c = OrdinaryIncidenceChains.vertexRepresentation g c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single v q =>
      rw [vertexRepresentation_single,OrdinaryIncidenceChains.vertexRepresentation_single]
      congr 1
@[simp] theorem cycleAction_K (g : GoodBuilding.K) (c : OrdinaryIncidenceChains.Cycles) :
    cycleAction (integral g.val) c = OrdinaryIncidenceChains.complex.cyclesAction g c := by
  apply Subtype.ext
  exact edgeRepresentation_K g c.val

end TernaryPoly.OrdinaryFullAction
