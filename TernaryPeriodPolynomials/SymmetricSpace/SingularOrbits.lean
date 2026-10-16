module

public import TernaryPeriodPolynomials.Topology.Covering.SingularFibers
public import TernaryPeriodPolynomials.SymmetricSpace.Covering

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceCovering
open CategoryTheory FreeActionLinearization CoveringSingularOrbits SymmetricSpacePositive

/-- The literal arithmetic covering as a morphism of topological spaces. -/
def singularCoveringProjection : TopCat.of Space ⟶ TopCat.of OrbitSpace :=
  TopCat.ofHom ⟨quotientProjection,quotientProjection_covering.continuous⟩

/-- Actual singular simplices on the arithmetic quotient are exactly deck orbits. -/
def actual_singular_orbit_equiv (n : ℕ) :
    MulAction.orbitRel.Quotient DeckGroup (SingularSimplex (TopCat.of Space) n) ≃
      SingularSimplex (TopCat.of OrbitSpace) n :=
  orbitEquiv singularCoveringProjection quotientProjection_quotientCovering n

/-- Every actual singular simplex on the arithmetic quotient lifts. -/
theorem actual_singular_projection_surjective (n : ℕ) :
    Function.Surjective (projection singularCoveringProjection n) :=
  projection_surjective singularCoveringProjection quotientProjection_quotientCovering n

/-- Actual lift sets identify with the actual covering fiber at the first vertex. -/
def actual_singular_lift_fiber_equiv {n : ℕ} (σ : SingularSimplex (TopCat.of OrbitSpace) n) :
    Lifts singularCoveringProjection σ ≃ Fiber singularCoveringProjection (atVertex σ) :=
  liftVertexEquiv singularCoveringProjection quotientProjection_quotientCovering σ

end TernaryPoly.SymmetricSpaceCovering
