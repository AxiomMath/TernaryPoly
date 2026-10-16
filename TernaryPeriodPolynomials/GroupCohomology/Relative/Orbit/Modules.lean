module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Cosets
public import TernaryPeriodPolynomials.GroupCohomology.Relative.PermutationModules

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeOrbitModules
open ModThreeGoodAction RelativeOrbitStabilizers RelativeOrbitCosets OrdinaryRelativeGraph

abbrev VertexCosets := ((K ⧸ HL) →₀ ℚ) × ((K ⧸ HP) →₀ ℚ)
abbrev EdgeCosets := ((K ⧸ HBB) →₀ ℚ) × ((K ⧸ HBG) →₀ ℚ)

/-- The actual relative vertex quotient is the two asserted stabilizer-coset permutation modules. -/
def relativeVertices : VertexCosets ≃ₗ[ℚ] R₀ :=
  (lineChains.prodCongr planeChains).trans RelativePermutationModules.vertexEquiv.symm

/-- The actual relative edge quotient is the two asserted flag-stabilizer coset modules. -/
def relativeEdges : EdgeCosets ≃ₗ[ℚ] R₁ :=
  (bbChains.prodCongr bgChains).trans RelativePermutationModules.edgeEquiv.symm

def vertexCosetLinear (g : K) : VertexCosets ≃ₗ[ℚ] VertexCosets :=
  (cosetLinear HL g).prodCongr (cosetLinear HP g)
def edgeCosetLinear (g : K) : EdgeCosets ≃ₗ[ℚ] EdgeCosets :=
  (cosetLinear HBB g).prodCongr (cosetLinear HBG g)

theorem vertex_coordinates (c : VertexCosets) :
    RelativePermutationModules.vertexEquiv (relativeVertices c) = (lineChains c.1,planeChains c.2) :=
  RelativePermutationModules.vertexEquiv.apply_symm_apply _
theorem edge_coordinates (c : EdgeCosets) :
    RelativePermutationModules.edgeEquiv (relativeEdges c) = (bbChains c.1,bgChains c.2) :=
  RelativePermutationModules.edgeEquiv.apply_symm_apply _

/-- The coset-module identification is equivariant for the actual quotient K representation. -/
theorem relativeVertices_equivariant (g : K) (c : VertexCosets) :
    relativeVertices (vertexCosetLinear g c) = OrdinaryRelativeGraphAction.vertexAction g (relativeVertices c) := by
  apply RelativePermutationModules.vertexEquiv.injective
  rw [vertex_coordinates,RelativePermutationModules.vertexEquiv_equivariant,vertex_coordinates]
  change (lineChains (cosetLinear HL g c.1),planeChains (cosetLinear HP g c.2)) = _
  rw [lineChains_equivariant,planeChains_equivariant]
  rfl

theorem relativeEdges_equivariant (g : K) (c : EdgeCosets) :
    relativeEdges (edgeCosetLinear g c) = OrdinaryRelativeGraphAction.edgeAction g (relativeEdges c) := by
  apply RelativePermutationModules.edgeEquiv.injective
  rw [edge_coordinates,RelativePermutationModules.edgeEquiv_equivariant,edge_coordinates]
  change (bbChains (cosetLinear HBB g c.1),bgChains (cosetLinear HBG g c.2)) = _
  rw [bbChains_equivariant,bgChains_equivariant]
  rfl

/-- The literal four stabilizer-coset modules, with their actual K-actions, identify both relative terms. -/
theorem coset_permutation_identification :
    (∀ g c, relativeVertices (vertexCosetLinear g c) = OrdinaryRelativeGraphAction.vertexAction g (relativeVertices c)) ∧
    (∀ g c, relativeEdges (edgeCosetLinear g c) = OrdinaryRelativeGraphAction.edgeAction g (relativeEdges c)) :=
  ⟨relativeVertices_equivariant,relativeEdges_equivariant⟩

end TernaryPoly.RelativeOrbitModules
