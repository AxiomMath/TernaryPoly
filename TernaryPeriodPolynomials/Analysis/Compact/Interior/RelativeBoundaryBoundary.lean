module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundarySupport

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex
open SingularLocalSupport SingularLocalCoefficient SingularCoverNaturality EquivariantSingularSmall
open SingularBoundaryRestriction SingularLocalCompactDuality
open SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix
  IntegralGL3Congruence

/-- The boundary covering retains its actual quotient-covering fact. -/
instance boundaryCoverFact : Fact (IsQuotientCoveringMap boundaryProjection principalSix) :=
  ⟨boundaryQuotientCovering⟩

/-- The equivariant/geometric boundary square gives the actual relative kernel isomorphism. -/
def boundaryGeometricIso (V : Rep.{0} ℚ principalSix) :
    relativeCochains V ≅ geometricRelativeCochains V :=
  kernel.mapIso (boundaryRestriction V) (geometricBoundaryRestriction V)
    (cochainIso wholeProjection wholeQuotientCovering V)
    (cochainIso boundaryProjection boundaryQuotientCovering V) (boundary_cochainIso_square V)

/-- The actual boundary kernel comparison retains literal relative-to-absolute inclusion. -/
theorem boundaryGeometricIso_inclusion (V : Rep.{0} ℚ principalSix) :
    (boundaryGeometricIso V).hom ≫ kernel.ι (geometricBoundaryRestriction V) =
      relativeInclusion V ≫ (cochainIso wholeProjection wholeQuotientCovering V).hom := by
  unfold boundaryGeometricIso
  erw [kernel.lift_ι]

/-- The inverse actual boundary kernel comparison retains the same ambient geometric cochain. -/
theorem boundaryGeometricIso_inv_inclusion (V : Rep.{0} ℚ principalSix) :
    (boundaryGeometricIso V).inv ≫ relativeInclusion V ≫
      (cochainIso wholeProjection wholeQuotientCovering V).hom = kernel.ι (geometricBoundaryRestriction V) := by
  rw [← boundaryGeometricIso_inclusion,Iso.inv_hom_id_assoc]

/-- The literal boundary covering equals the restriction to its actual covering preimage
through the existing set-equality homeomorphism, with the same boundary base. -/
def boundaryCoverHomeomorph : CoverHomeomorph (G := principalSix) boundaryProjection
    (restrictedProjection wholeProjection (boundary principalSix)) where
  total := boundaryPreimageHomeomorph
  base := Homeomorph.refl _
  square := rfl
  equivariant _ _ := rfl

/-- The actual boundary geometric restriction is the literal preimage restriction followed
by the genuine covering-homeomorphism pullback. -/
theorem boundaryRestriction_square (V : Rep.{0} ℚ principalSix) :
    localRestriction wholeProjection (boundary principalSix) V ≫
      coveringCochainMap boundaryCoverHomeomorph V = geometricBoundaryRestriction V := by
  unfold localRestriction coveringCochainMap
  erw [← localPullback_comp]
  rfl

/-- Support in the entire open interior means vanishing on exactly the actual boundary. -/
def supportAtInteriorIso (V : Rep.{0} ℚ principalSix) :
    supportCochains wholeProjection V interiorOpen ≅ geometricRelativeCochains V := by
  have := coveringCochainMap_isIso boundaryCoverHomeomorph V
  exact kernel.mapIso (localRestriction wholeProjection (boundary principalSix) V)
    (geometricBoundaryRestriction V) (Iso.refl _) (asIso (coveringCochainMap boundaryCoverHomeomorph V))
    (by change _ = 𝟙 _ ≫ _; rw [Category.id_comp]; exact boundaryRestriction_square V)

/-- The whole-interior support comparison preserves literal ambient geometric cochains. -/
theorem supportAtInteriorIso_inclusion (V : Rep.{0} ℚ principalSix) :
    (supportAtInteriorIso V).hom ≫ kernel.ι (geometricBoundaryRestriction V) =
      supportInclusion wholeProjection V interiorOpen := by
  unfold supportAtInteriorIso
  erw [kernel.lift_ι]
  exact Category.comp_id _

/-- The actual boundary-relative Hom quotient model equals the equivariant relative
cochain kernel by literal ambient inclusions and the proved covering preimage comparison. -/
def ambientBoundaryIso (V : Rep.{0} ℚ principalSix) :
    ambientRelativeCochains (boundary principalSix) V ≅ relativeCochains V :=
  supportRelativeIso interiorOpen V ≪≫ supportAtInteriorIso V ≪≫ (boundaryGeometricIso V).symm

/-- The actual boundary-relative model comparison retains the literal ambient equivariant cochain. -/
theorem ambientBoundaryIso_inclusion (V : Rep.{0} ℚ principalSix) :
    (ambientBoundaryIso V).hom ≫ relativeInclusion V = ambientRelativeInclusion (boundary principalSix) V := by
  have h₁ : ((supportAtInteriorIso V).hom ≫ (boundaryGeometricIso V).inv) ≫
      (relativeInclusion V ≫ (cochainIso wholeProjection wholeQuotientCovering V).hom) =
        supportInclusion wholeProjection V interiorOpen := by
    rw [Category.assoc,boundaryGeometricIso_inv_inclusion,supportAtInteriorIso_inclusion]
  have h₂ := congrArg (fun f => (supportRelativeIso interiorOpen V).hom ≫ f) h₁
  have h₃ := supportRelativeIso_inclusion (interiorOpen : Set BordifiedOrbit) V
  apply (cancel_mono (cochainIso wholeProjection wholeQuotientCovering V).hom).mp
  change ((supportRelativeIso interiorOpen V).hom ≫ ((supportAtInteriorIso V).hom ≫
    (boundaryGeometricIso V).inv)) ≫ (relativeInclusion V ≫
      (cochainIso wholeProjection wholeQuotientCovering V).hom) = _
  exact (Category.assoc _ _ _).trans (h₂.trans h₃)

end TernaryPoly.CompactInteriorRelativeBoundary
