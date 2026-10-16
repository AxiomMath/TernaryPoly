module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryColimit
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryCompatibility

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex
open SingularLocalSupport SingularLocalCoefficient SingularCoverNaturality EquivariantSingularSmall
open SingularBoundaryRestriction SymmetricSpaceBordifiedCohomology IntegralGL3Congruence

variable (V : Rep.{0} ℚ principalSix)

/-- The genuine compactly supported cohomology of the arithmetic interior is the genuine
relative cohomology of its compact bordification, for arbitrary coefficients and all degrees. -/
def compactRelativeIso (k : ℕ) : compactCohomology interiorCover V k ≅ (relativeCochains V).homology k :=
  interiorCompactIso V k ≪≫ openCompactBoundaryIso V k ≪≫
    (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) k).mapIso (ambientBoundaryIso V)

/-- The actual compact/relative comparison has the literal excision-and-boundary formula. -/
theorem compactRelativeIso_hom (k : ℕ) :
    (compactRelativeIso V k).hom = (interiorCompactIso V k).hom ≫ compactToBoundary V k ≫
      homologyMap (ambientBoundaryIso V).hom k := rfl

/-- The actual boundary-model cochain comparison preserves the interior restriction. -/
theorem ambientBoundaryIso_toInterior :
    (ambientBoundaryIso V).hom ≫ relativeInclusion V ≫
      (cochainIso wholeProjection wholeQuotientCovering V).hom ≫ interiorRestriction V =
      ambientInteriorMap V (SymmetricSpaceBordifiedQuotient.boundary principalSix) ≫
        SingularLocalCompactDuality.coveringCochainMap interiorCoverHomeomorph V := by
  calc
    _ = ((ambientBoundaryIso V).hom ≫ relativeInclusion V) ≫
        (cochainIso wholeProjection wholeQuotientCovering V).hom ≫ interiorRestriction V :=
      (Category.assoc _ _ _).symm
    _ = ambientRelativeInclusion (SymmetricSpaceBordifiedQuotient.boundary principalSix) V ≫
        (cochainIso wholeProjection wholeQuotientCovering V).hom ≫ interiorRestriction V :=
      congrArg (fun f => f ≫ (cochainIso wholeProjection wholeQuotientCovering V).hom ≫
        interiorRestriction V) (ambientBoundaryIso_inclusion V)
    _ = ambientRelativeInclusion (SymmetricSpaceBordifiedQuotient.boundary principalSix) V ≫
        (cochainIso wholeProjection wholeQuotientCovering V).hom ≫
          (localRestriction wholeProjection interiorOpen V ≫
            SingularLocalCompactDuality.coveringCochainMap interiorCoverHomeomorph V) :=
      congrArg (fun f => ambientRelativeInclusion (SymmetricSpaceBordifiedQuotient.boundary principalSix) V ≫
        (cochainIso wholeProjection wholeQuotientCovering V).hom ≫ f) (interiorRestriction_square V).symm
    _ = _ := by
      change _ = (_ ≫ _ ≫ _) ≫ _
      simp only [Category.assoc]

/-- The actual boundary-model comparison retains the same interior restriction on cohomology. -/
theorem ambientBoundaryIso_toInterior_homology (k : ℕ) :
    homologyMap (ambientBoundaryIso V).hom k ≫ homologyMap (relativeInclusion V) k ≫
      homologyMap (cochainIso wholeProjection wholeQuotientCovering V).hom k ≫
        homologyMap (interiorRestriction V) k =
      homologyMap (ambientInteriorMap V (SymmetricSpaceBordifiedQuotient.boundary principalSix)) k ≫
        homologyMap (SingularLocalCompactDuality.coveringCochainMap interiorCoverHomeomorph V) k := by
  have h := congrArg (fun f => homologyMap f k) (ambientBoundaryIso_toInterior V)
  simp only [homologyMap_comp] at h
  erw [homologyMap_comp (cochainIso wholeProjection wholeQuotientCovering V).hom
    (interiorRestriction V) k] at h
  exact h

/-- The actual relative-to-absolute inclusion followed by the interior restriction
agrees exactly with the actual compact-support-to-ordinary map. -/
theorem compactRelativeIso_toOrdinary (k : ℕ) :
    (compactRelativeIso V k).hom ≫ relativeToAbsolute V k ≫
      homologyMap (cochainIso wholeProjection wholeQuotientCovering V).hom k ≫
      homologyMap (interiorRestriction V) k = compactForget interiorCover V k := by
  rw [compactRelativeIso_hom]
  change (_ ≫ _ ≫ homologyMap _ k) ≫ homologyMap (relativeInclusion V) k ≫ _ ≫ _ = _
  rw [Category.assoc,Category.assoc,ambientBoundaryIso_toInterior_homology,
    ← Category.assoc (compactToBoundary V k),compactToBoundary_forget]
  exact interiorCompactIso_forget V k

/-- The same genuine compact cohomology is the geometric local-coefficient relative cohomology
of the actual bordification and its entire boundary. -/
def compactGeometricRelativeIso (k : ℕ) :
    compactCohomology interiorCover V k ≅ (geometricRelativeCochains V).homology k :=
  compactRelativeIso V k ≪≫
    (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) k).mapIso (boundaryGeometricIso V)

/-- The compact geometric comparison is the literal equivariant comparison followed by
the actual kernel isomorphism induced by the boundary comparison square. -/
theorem compactGeometricRelativeIso_hom (k : ℕ) :
    (compactGeometricRelativeIso V k).hom = (compactRelativeIso V k).hom ≫
      homologyMap (boundaryGeometricIso V).hom k := rfl

/-- Literal geometric relative inclusion preserves the actual compact-to-ordinary map. -/
theorem compactGeometricRelativeIso_toOrdinary (k : ℕ) :
    (compactGeometricRelativeIso V k).hom ≫ homologyMap (kernel.ι (geometricBoundaryRestriction V)) k ≫
      homologyMap (interiorRestriction V) k = compactForget interiorCover V k := by
  have h := congrArg (fun f => homologyMap f k) (boundaryGeometricIso_inclusion V)
  simp only [homologyMap_comp] at h
  rw [compactGeometricRelativeIso_hom,Category.assoc]
  erw [← Category.assoc (homologyMap (boundaryGeometricIso V).hom k),h,Category.assoc]
  exact compactRelativeIso_toOrdinary V k

end TernaryPoly.CompactInteriorRelativeBoundary
