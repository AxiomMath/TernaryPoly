module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryNeighborhoods
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundarySupport
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryDeformationAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory HomologicalComplex EquivariantSingularSmall
open SingularBoundaryRestriction SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

/-- The literal boundary-relative pullback of the quotient from a neighborhood-relative complex. -/
def boundaryRelativeMap (W : Set BordifiedOrbit) (hAW : boundary principalSix ⊆ W)
    (V : Rep.{0} ℚ principalSix) : ambientRelativeCochains W V ⟶ ambientRelativeCochains (boundary principalSix) V :=
  relativeToBoundary (wholeProjection ⁻¹' boundary principalSix) (wholeProjection ⁻¹' W)
    (Set.preimage_mono hAW) V

/-- The literal relative transition associated to shrinking actual boundary neighborhoods. -/
def boundaryNeighborhoodMap (W N : Set BordifiedOrbit) (hNW : N ⊆ W)
    (V : Rep.{0} ℚ principalSix) : ambientRelativeCochains W V ⟶ ambientRelativeCochains N V :=
  relativeNeighborhoodTransition (wholeProjection ⁻¹' W) (wholeProjection ⁻¹' N) V (Set.preimage_mono hNW)

variable {W : Set BordifiedOrbit} (c : SymmetricSpaceBoundaryNeighborhood.Collapse W)
  (V : Rep.{0} ℚ principalSix)

/-- The actual equivariant lifted endpoint pulls boundary-relative cochains back to the
relative cochains of the whole cover modulo its smaller boundary neighborhood. -/
def endpointPullback : ambientRelativeCochains (boundary principalSix) V ⟶
    ambientRelativeCochains c.neighborhood V :=
  relativeFromBoundary (wholeProjection ⁻¹' boundary principalSix) (wholeProjection ⁻¹' W)
    (CoveringBoundaryDeformation.Actual.deformation c)
    (CoveringBoundaryDeformation.Actual.deformation_equivariant c)
    (wholeProjection ⁻¹' c.neighborhood)
    (fun x hx => (boundary_iff _).mp (CoveringBoundaryDeformation.Actual.endpoint_mem c ⟨x,hx⟩)) V

/-- The actual endpoint supplies a right inverse to boundary-relative restriction in every degree. -/
theorem endpointPullback_retraction (k : ℕ) :
    homologyMap (endpointPullback c V) k ≫
      homologyMap (boundaryRelativeMap c.neighborhood c.contains_boundary V) k = 𝟙 _ :=
  relativeFromBoundary_retraction (wholeProjection ⁻¹' boundary principalSix) (wholeProjection ⁻¹' W)
    (CoveringBoundaryDeformation.Actual.deformation c)
    (CoveringBoundaryDeformation.Actual.deformation_equivariant c)
    (wholeProjection ⁻¹' c.neighborhood) (Set.preimage_mono c.contains_boundary) _ V k

/-- Actual boundary restriction and endpoint lifting equal the genuine smaller-neighborhood
transition on cohomology, giving eventual annihilation for every degree and every representation. -/
theorem endpointPullback_transition (hAW : boundary principalSix ⊆ W) (k : ℕ) :
    homologyMap (boundaryRelativeMap W hAW V) k ≫ homologyMap (endpointPullback c V) k =
      homologyMap (boundaryNeighborhoodMap W c.neighborhood c.subset V) k :=
  relativeFromBoundary_transition (wholeProjection ⁻¹' boundary principalSix) (wholeProjection ⁻¹' W)
    (CoveringBoundaryDeformation.Actual.deformation c)
    (CoveringBoundaryDeformation.Actual.deformation_equivariant c)
    (wholeProjection ⁻¹' c.neighborhood) _ V (Set.preimage_mono hAW) (Set.preimage_mono c.subset) k

end TernaryPoly.CompactInteriorRelativeBoundary
