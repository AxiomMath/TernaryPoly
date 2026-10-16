module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Relative.Graph

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryRelativeGraphAction
open OrdinaryIncidenceChains OrdinaryRelativeGraph

/-- The three actual Good image subspaces are stable under the same K action. -/
theorem goodEdges_stable (g : GoodBuilding.K) :
    goodEdges ≤ goodEdges.comap (edgeRepresentation g) := by
  rintro _ ⟨c,rfl⟩
  exact ⟨GoodChainComplex.edgeRepresentation g c,edgeInclusion_equivariant g c⟩
theorem goodVertices_stable (g : GoodBuilding.K) :
    goodVertices ≤ goodVertices.comap (vertexRepresentation g) := by
  rintro _ ⟨c,rfl⟩
  exact ⟨GoodChainComplex.vertexRepresentation g c,vertexInclusion_equivariant g c⟩
theorem goodCycles_stable (g : GoodBuilding.K) :
    goodCycles ≤ goodCycles.comap (complex.cyclesAction g) := by
  rintro _ ⟨c,rfl⟩
  exact ⟨GoodChainComplex.complex.cyclesAction g c,cycleInclusion_equivariant g c⟩

/-- The genuine quotient representations on relative edges, vertices, and cycles. -/
def edgeAction : Representation ℚ GoodBuilding.K R₁ :=
  edgeRepresentation.quotient goodEdges goodEdges_stable
def vertexAction : Representation ℚ GoodBuilding.K R₀ :=
  vertexRepresentation.quotient goodVertices goodVertices_stable
def cycleAction : Representation ℚ GoodBuilding.K Q :=
  complex.cyclesAction.quotient goodCycles goodCycles_stable

@[simp] theorem edgeAction_mk (g : GoodBuilding.K) (c : EdgeChains) :
    edgeAction g (Submodule.Quotient.mk c) = Submodule.Quotient.mk (edgeRepresentation g c) := rfl
@[simp] theorem vertexAction_mk (g : GoodBuilding.K) (c : VertexChains) :
    vertexAction g (Submodule.Quotient.mk c) = Submodule.Quotient.mk (vertexRepresentation g c) := rfl
@[simp] theorem cycleAction_mk (g : GoodBuilding.K) (c : Cycles) :
    cycleAction g (Submodule.Quotient.mk c) = Submodule.Quotient.mk (complex.cyclesAction g c) := rfl

/-- The injection in the relative graph sequence commutes with the actual K actions. -/
theorem cycleToEdge_equivariant (g : GoodBuilding.K) (x : Q) :
    cycleToEdge (cycleAction g x) = edgeAction g (cycleToEdge x) := by
  refine Submodule.Quotient.induction_on goodCycles x ?_
  intro c
  rfl

/-- The relative boundary commutes with the actual K actions. -/
theorem relativeBoundary_equivariant (g : GoodBuilding.K) (x : R₁) :
    relativeBoundary (edgeAction g x) = vertexAction g (relativeBoundary x) := by
  refine Submodule.Quotient.induction_on goodEdges x ?_
  intro c
  change goodVertices.mkQ (boundary (edgeRepresentation g c)) =
    goodVertices.mkQ (vertexRepresentation g (boundary c))
  rw [boundary_equivariant]

/-- The literal ordinary/Good graph quotients form a K-equivariant short exact sequence. -/
theorem equivariant_short_exact :
    Function.Injective cycleToEdge ∧ cycleToEdge.range = relativeBoundary.ker ∧
    Function.Surjective relativeBoundary ∧
    (∀ g x, cycleToEdge (cycleAction g x) = edgeAction g (cycleToEdge x)) ∧
    (∀ g x, relativeBoundary (edgeAction g x) = vertexAction g (relativeBoundary x)) :=
  ⟨cycleToEdge_injective,range_cycleToEdge,relativeBoundary_surjective,
    cycleToEdge_equivariant,relativeBoundary_equivariant⟩

end TernaryPoly.OrdinaryRelativeGraphAction
