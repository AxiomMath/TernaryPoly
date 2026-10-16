module

public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionSurjective
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionGeometry

@[expose] public section


noncomputable section
open CategoryTheory HomologicalComplex
namespace TernaryPoly.SingularBoundaryRestriction
open EquivariantSingularResolution EquivariantSingularCohomology SingularCoverNaturality
  SingularLocalCoefficient IntegralGL3Congruence SymmetricSpaceRationalGluing

/-- Equivariant singular Hom cochains on the actual whole bordification. -/
abbrev absoluteCochains (V : Rep ℚ principalSix) := cochains principalSix (TopCat.of Glued) V

/-- Equivariant singular Hom cochains on its actual invariant boundary. -/
abbrev boundaryCochains (V : Rep ℚ principalSix) := cochains principalSix (TopCat.of BoundaryCover) V

/-- Literal cochain restriction induced by the actual boundary inclusion. -/
def boundaryRestriction (V : Rep ℚ principalSix) : absoluteCochains V ⟶ boundaryCochains V :=
  cochainPullback boundaryInclusion boundaryInclusion_equivariant V

/-- Actual boundary restriction is surjective in every cochain degree. -/
theorem boundaryRestriction_surjective (V : Rep ℚ principalSix) (n : ℕ) :
    Function.Surjective ((boundaryRestriction V).f n) :=
  cochainPullback_surjective boundaryInclusion boundaryInclusion_equivariant
    boundaryInclusion_injective V n

/-- The same actual restriction on geometric local-system singular cochains downstairs. -/
def geometricBoundaryRestriction (V : Rep ℚ principalSix) :
    localCochains wholeProjection wholeQuotientCovering V ⟶
      localCochains boundaryProjection boundaryQuotientCovering V :=
  localPullback boundaryProjection wholeProjection boundaryInclusion boundaryBaseInclusion
    boundary_square boundaryQuotientCovering wholeQuotientCovering boundaryInclusion_equivariant V

/-- The literal singular/local-coefficient isomorphisms identify the actual boundary restriction. -/
theorem boundary_cochainIso_square (V : Rep ℚ principalSix) :
    boundaryRestriction V ≫ (cochainIso boundaryProjection boundaryQuotientCovering V).hom=
      (cochainIso wholeProjection wholeQuotientCovering V).hom ≫ geometricBoundaryRestriction V :=
  cochainIso_pullback boundaryProjection wholeProjection boundaryInclusion boundaryBaseInclusion
    boundary_square boundaryQuotientCovering wholeQuotientCovering boundaryInclusion_equivariant V

/-- Literal geometric local-system restriction is degreewise surjective as well. -/
theorem geometricBoundaryRestriction_surjective (V : Rep ℚ principalSix) (n : ℕ) :
    Function.Surjective ((geometricBoundaryRestriction V).f n) := by
  intro c
  obtain ⟨c,rfl⟩ := (homVertexEquiv boundaryProjection boundaryQuotientCovering V n).surjective c
  obtain ⟨d,hd⟩ := boundaryRestriction_surjective V n c
  refine ⟨homVertexEquiv wholeProjection wholeQuotientCovering V n d,?_⟩
  exact (homVertexEquiv_pullback boundaryProjection wholeProjection boundaryInclusion boundaryBaseInclusion
    boundary_square boundaryQuotientCovering wholeQuotientCovering boundaryInclusion_equivariant V n d).symm.trans
      (congrArg (homVertexEquiv boundaryProjection boundaryQuotientCovering V n) hd)

end TernaryPoly.SingularBoundaryRestriction
