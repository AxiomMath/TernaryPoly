module

public import TernaryPeriodPolynomials.Building.Good.Building
public import TernaryPeriodPolynomials.Building.BipartitePathChains
public import TernaryPeriodPolynomials.Building.Path.FixedVertex
public import TernaryPeriodPolynomials.Polynomial.GLAction
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section

/-! The actual rational incidence chains of the good building, their path class,
and its vanishing on good-vertex stabilizers. The map from cycles to polynomial
coefficients is an explicit hypothesis throughout. -/

noncomputable section
open CategoryTheory
namespace TernaryPoly.GoodChainComplex

open GoodBuilding
open TernaryPeriodPolynomial.PathCocycle

/-- Strict incidence between an actual good line and an actual good plane. -/
def incidence (L : GoodLine) (P : GoodPlane) : Prop := L.val < P.val

abbrev GoodEdge := BipartitePathChains.Edge incidence
abbrev EdgeChains := BipartitePathChains.Chain₁ incidence
abbrev VertexChains := BipartitePathChains.Chain₀ GoodLine GoodPlane

/-- An integral matrix in K permutes the actual oriented incidence edges. -/
def edgeAction (g : K) : Equiv.Perm GoodEdge :=
  BipartitePathChains.edgeEquiv (lineAction g) (planeAction g)
    (fun L P => (incidence_action_iff g L P).symm)

@[simp] theorem edgeAction_one (a : GoodEdge) : edgeAction 1 a = a := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact ModThreeGoodAction.act_one a.val.1.val
  · apply Subtype.ext
    exact ModThreeGoodAction.act_one a.val.2.val

@[simp] theorem edgeAction_mul (g h : K) (a : GoodEdge) :
    edgeAction (g * h) a = edgeAction g (edgeAction h a) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact ModThreeGoodAction.act_mul g h a.val.1.val
  · apply Subtype.ext
    exact ModThreeGoodAction.act_mul g h a.val.2.val

/-- Linear extension of the actual edge permutation. -/
def edgeLinear (g : K) : EdgeChains ≃ₗ[ℚ] EdgeChains :=
  BipartitePathChains.chainEquiv (lineAction g) (planeAction g)
    (fun L P => (incidence_action_iff g L P).symm)

@[simp] theorem edgeLinear_single (g : K) (a : GoodEdge) (c : ℚ) :
    edgeLinear g (Finsupp.single a c) = Finsupp.single (edgeAction g a) c :=
  BipartitePathChains.chainEquiv_single _ _ _ _ _

/-- The actual rational edge-chain representation. -/
def edgeRepresentation : Representation ℚ K EdgeChains where
  toFun g := (edgeLinear g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro c
    change edgeLinear 1 c = c
    induction c using Finsupp.induction_linear with
    | zero => exact map_zero _
    | add c d hc hd => rw [map_add, hc, hd]
    | single a q => rw [edgeLinear_single, edgeAction_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    change edgeLinear (g * h) c = edgeLinear g (edgeLinear h c)
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add c d hc hd => simp only [map_add, hc, hd]
    | single a q => simp only [edgeLinear_single, edgeAction_mul]

@[simp] theorem edgeRepresentation_single (g : K) (a : GoodEdge) (c : ℚ) :
    edgeRepresentation g (Finsupp.single a c) = Finsupp.single (edgeAction g a) c :=
  edgeLinear_single g a c

/-- Linear extension of the actual good-vertex permutation. -/
def vertexLinear (g : K) : VertexChains ≃ₗ[ℚ] VertexChains :=
  BipartitePathChains.vertexChainEquiv (lineAction g) (planeAction g)

@[simp] theorem vertexLinear_single (g : K) (v : GoodVertex) (c : ℚ) :
    vertexLinear g (Finsupp.single v c) = Finsupp.single (g • v) c :=
  BipartitePathChains.vertexChainEquiv_single _ _ _ _

/-- The actual rational vertex-chain representation. -/
def vertexRepresentation : Representation ℚ K VertexChains where
  toFun g := (vertexLinear g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro c
    change vertexLinear 1 c = c
    induction c using Finsupp.induction_linear with
    | zero => exact map_zero _
    | add c d hc hd => rw [map_add, hc, hd]
    | single v q => rw [vertexLinear_single, one_smul]
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    change vertexLinear (g * h) c = vertexLinear g (vertexLinear h c)
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v q => simp only [vertexLinear_single, mul_smul]

@[simp] theorem vertexRepresentation_single (g : K) (v : GoodVertex) (c : ℚ) :
    vertexRepresentation g (Finsupp.single v c) = Finsupp.single (g • v) c :=
  vertexLinear_single g v c

/-- The actual line-to-plane incidence boundary. -/
def boundary : EdgeChains →ₗ[ℚ] VertexChains := BipartitePathChains.boundary incidence

/-- The incidence boundary commutes with the genuine K-actions. -/
theorem boundary_equivariant (g : K) (c : EdgeChains) :
    boundary (edgeRepresentation g c) = vertexRepresentation g (boundary c) :=
  BipartitePathChains.boundary_chainEquiv (lineAction g) (planeAction g)
    (fun L P => (incidence_action_iff g L P).symm) c

/-- The degree-one and degree-zero chain complex of the actual good building. -/
def complex : BoundaryData K EdgeChains VertexChains where
  chains := edgeRepresentation
  vertices := vertexRepresentation
  boundary := boundary
  equivariant := boundary_equivariant

/-- Cycles are the kernel of the actual incidence boundary. -/
abbrev Cycles := complex.Cycles

/-- The concrete good-building graph is the incidence graph used for chains. -/
def incidenceGraphIso : GoodBuilding.graph ≃g BipartitePathChains.graph incidence where
  toEquiv := Equiv.refl GoodVertex
  map_rel_iff' := by
    intro u v
    cases u <;> cases v <;> rfl

/-- The actual chosen path, viewed in the chain complex's incidence graph. -/
def pathWalk (v : GoodVertex) :
    (BipartitePathChains.graph incidence).Walk baseVertex v :=
  (GoodBuilding.pathFromBase v).val.map incidenceGraphIso.toHom

/-- These actual paths use at most four incidence edges. -/
theorem pathWalk_length_le_four (v : GoodVertex) : (pathWalk v).length ≤ 4 := by
  exact (SimpleGraph.Walk.length_map incidenceGraphIso.toHom
    (GoodBuilding.pathFromBase v).val).trans_le (GoodBuilding.pathFromBase_length_le_four v)

/-- The chain of the actual chosen finite path, oriented toward the base vertex. -/
def pathToBase (v : GoodVertex) : EdgeChains :=
  -BipartitePathChains.walkChain incidence (pathWalk v)

@[simp] theorem boundary_pathToBase (v : GoodVertex) :
    boundary (pathToBase v) = Finsupp.single baseVertex 1 - Finsupp.single v 1 := by
  change BipartitePathChains.boundary incidence
    (-BipartitePathChains.walkChain incidence (pathWalk v)) = _
  rw [map_neg, BipartitePathChains.boundary_walkChain, neg_sub]

/-- The actual first-coordinate vertex as a zero-chain. -/
def baseChain : VertexChains := Finsupp.single baseVertex 1

/-- The actual path family has boundary base minus its translate. -/
def paths : complex.Paths baseChain where
  path g := pathToBase (g • baseVertex)
  boundary_path g := by
    change boundary (pathToBase (g • baseVertex)) =
      Finsupp.single baseVertex 1 - vertexRepresentation g (Finsupp.single baseVertex 1)
    rw [boundary_pathToBase, vertexRepresentation_single]

/-- Restriction of any cycle-map path class to every good-vertex stabilizer vanishes. -/
theorem pathClass_restrict_stabilizer_eq_zero {E : Type} [AddCommGroup E] [Module ℚ E]
    (F : complex.CycleMap E) (v : GoodVertex) :
    groupCohomology.map (MulAction.stabilizer K v).subtype
      (𝟙 (Rep.res (MulAction.stabilizer K v).subtype (Rep.of F.action))) 2
      (F.pathClass paths) = 0 := by
  apply F.pathClass_restrict_eq_zero_of_fixed_vertex paths (MulAction.stabilizer K v)
    (Finsupp.single v 1) (pathToBase v)
  · exact boundary_pathToBase v
  · intro g hg
    change vertexRepresentation g (Finsupp.single v 1) = Finsupp.single v 1
    rw [vertexRepresentation_single, MulAction.mem_stabilizer_iff.mp hg]

/-- The exact homogeneous coefficient representation, restricted from integral matrices to K. -/
def coefficientAction (n : ℕ) (e : ℤ) :
    Representation ℚ K (PolynomialGLAction.HomogeneousPoly n) :=
  (PolynomialGLAction.integralAction n e).comp ModThreeGoodAction.K.subtype

/-- Explicit equivariant linear evaluation of actual cycles in the homogeneous coefficients. -/
structure PolynomialCycleMap (n : ℕ) (e : ℤ) where
  map : Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n
  equivariant : ∀ (g : K) (c : Cycles),
    map (complex.cyclesAction g c) = coefficientAction n e g (map c)

namespace PolynomialCycleMap

variable {n : ℕ} {e : ℤ} (F : PolynomialCycleMap n e)

/-- A polynomial-valued cycle map with the stipulated concrete coefficient action. -/
def toCycleMap : complex.CycleMap (PolynomialGLAction.HomogeneousPoly n) where
  action := coefficientAction n e
  map := F.map
  equivariant := F.equivariant

/-- The genuine degree-two group cohomology class of the good-building path defect. -/
def pathClass : groupCohomology.H2 (Rep.of (coefficientAction n e)) :=
  F.toCycleMap.pathClass paths

/-- The class vanishes after restriction to the stabilizer of every actual good vertex. -/
theorem restrict_stabilizer_eq_zero (v : GoodVertex) :
    groupCohomology.map (MulAction.stabilizer K v).subtype
      (𝟙 (Rep.res (MulAction.stabilizer K v).subtype (Rep.of (coefficientAction n e)))) 2
      F.pathClass = 0 :=
  pathClass_restrict_stabilizer_eq_zero F.toCycleMap v

end PolynomialCycleMap
end TernaryPoly.GoodChainComplex
