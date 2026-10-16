module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryDeformation

@[expose] public section

noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall
open EquivariantSingularPairHomotopy SingularCoverNaturality SingularLocalSupport SingularLocalCoefficient
open SingularBoundaryRestriction SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

/-- The actual relative neighborhood transition retains the same literal ambient cochain. -/
theorem boundaryNeighborhoodMap_inclusion (W N : Set BordifiedOrbit) (hNW : N ⊆ W)
    (V : Rep.{0} ℚ principalSix) :
    boundaryNeighborhoodMap W N hNW V ≫ ambientRelativeInclusion N V = ambientRelativeInclusion W V := by
  unfold boundaryNeighborhoodMap relativeNeighborhoodTransition relativeHomPullback ambientRelativeInclusion
  erw [← homPullback_comp,relativeMap_projection,chainMap_id,Category.id_comp]

/-- The actual boundary restriction retains the same literal ambient cochain. -/
theorem boundaryRelativeMap_inclusion (W : Set BordifiedOrbit) (hAW : boundary principalSix ⊆ W)
    (V : Rep.{0} ℚ principalSix) :
    boundaryRelativeMap W hAW V ≫ ambientRelativeInclusion (boundary principalSix) V =
      ambientRelativeInclusion W V := boundaryNeighborhoodMap_inclusion W _ hAW V

/-- Actual neighborhood restriction commutes with actual restriction to the full boundary. -/
theorem boundaryRelativeMap_transition (W N : Set BordifiedOrbit) (hNW : N ⊆ W)
    (hAN : boundary principalSix ⊆ N) (V : Rep.{0} ℚ principalSix) :
    boundaryNeighborhoodMap W N hNW V ≫ boundaryRelativeMap N hAN V =
      boundaryRelativeMap W (hAN.trans hNW) V := by
  unfold boundaryNeighborhoodMap relativeNeighborhoodTransition boundaryRelativeMap relativeToBoundary
  erw [relativeHomPullback_comp]
  simp only [Category.id_comp]

/-- Actual relative neighborhood transitions compose as literal inclusions of pairs. -/
theorem boundaryNeighborhoodMap_comp (W N P : Set BordifiedOrbit) (hNW : N ⊆ W) (hPN : P ⊆ N)
    (V : Rep.{0} ℚ principalSix) :
    boundaryNeighborhoodMap W N hNW V ≫ boundaryNeighborhoodMap N P hPN V =
      boundaryNeighborhoodMap W P (hPN.trans hNW) V := by
  unfold boundaryNeighborhoodMap relativeNeighborhoodTransition
  erw [relativeHomPullback_comp]
  simp only [Category.id_comp]

/-- Actual support enlargement is identified with the literal relative transition of
complementary covering neighborhoods. -/
theorem supportRelativeIso_natural (K L : Set BordifiedOrbit) (hKL : K ⊆ L)
    (V : Rep.{0} ℚ principalSix) :
    (supportRelativeIso K V).hom ≫ supportMap wholeProjection V K L hKL =
      boundaryNeighborhoodMap Kᶜ Lᶜ (Set.compl_subset_compl.mpr hKL) V ≫ (supportRelativeIso L V).hom := by
  apply (cancel_mono (supportInclusion wholeProjection V L)).mp
  rw [Category.assoc,supportMap_inclusion,supportRelativeIso_inclusion,Category.assoc,
    supportRelativeIso_inclusion,← Category.assoc,boundaryNeighborhoodMap_inclusion]

end TernaryPoly.CompactInteriorRelativeBoundary
