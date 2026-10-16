module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundarySupportNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport EquivariantSingularSmall SingularBoundaryRestriction
open SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

variable (V : Rep.{0} ℚ principalSix)

/-- Actual equivariant relative cohomology at the complementary boundary neighborhood is
identified with the actual fixed-support cohomology of the open interior by genuine excision. -/
def fixedSupportIso (K : Compacts interiorOpen) (k : ℕ) :
    (ambientRelativeCochains (outsideCompact K) V).homology k ≅
      (supportCochains (restrictedProjection wholeProjection interiorOpen) V K).homology k :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) k).mapIso
    (supportRelativeIso (openCompactImage interiorOpen K) V) ≪≫
      openSupportIso wholeProjection V interiorOpen K k

/-- Actual fixed-support excision identifies neighborhood restriction with literal support enlargement. -/
theorem fixedSupportIso_natural (K L : Compacts interiorOpen) (hKL : K ≤ L) (k : ℕ) :
    homologyMap (boundaryNeighborhoodMap (outsideCompact K) (outsideCompact L)
      (outsideCompact_antitone hKL) V) k ≫ (fixedSupportIso V L k).hom =
        (fixedSupportIso V K k).hom ≫
          homologyMap (supportMap (restrictedProjection wholeProjection interiorOpen) V K L hKL) k := by
  have h := congrArg (fun f => homologyMap f k)
    (supportRelativeIso_natural (openCompactImage interiorOpen K)
      (openCompactImage interiorOpen L) (Set.image_mono hKL) V)
  simp only [homologyMap_comp] at h
  change homologyMap _ k ≫ ((homologyMap _ k) ≫ (openSupportIso wholeProjection V interiorOpen L k).hom) =
    ((homologyMap _ k) ≫ (openSupportIso wholeProjection V interiorOpen K k).hom) ≫ homologyMap _ k
  erw [← Category.assoc,← h,Category.assoc]
  erw [openSupportIso_natural wholeProjection V interiorOpen K L hKL k,← Category.assoc]

/-- Inverse actual fixed-support excision is natural for support enlargement. -/
theorem fixedSupportIso_inv_natural (K L : Compacts interiorOpen) (hKL : K ≤ L) (k : ℕ) :
    homologyMap (supportMap (restrictedProjection wholeProjection interiorOpen) V K L hKL) k ≫
      (fixedSupportIso V L k).inv =
        (fixedSupportIso V K k).inv ≫ homologyMap
          (boundaryNeighborhoodMap (outsideCompact K) (outsideCompact L) (outsideCompact_antitone hKL) V) k := by
  apply (cancel_mono (fixedSupportIso V L k).hom).mp
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id,Category.assoc,fixedSupportIso_natural,
    Iso.inv_hom_id_assoc]

/-- The literal comparison sends a fixed compact-support class through inverse excision
and actual restriction to the entire boundary-relative Hom complex. -/
def fixedToBoundary (K : Compacts interiorOpen) (k : ℕ) :
    (supportCochains (restrictedProjection wholeProjection interiorOpen) V K).homology k ⟶
      (ambientRelativeCochains (SymmetricSpaceBordifiedQuotient.boundary principalSix) V).homology k :=
  (fixedSupportIso V K k).inv ≫
    homologyMap (boundaryRelativeMap (outsideCompact K) (boundary_subset_outsideCompact K) V) k

/-- The actual fixed-support comparison is compatible with every support enlargement. -/
theorem fixedToBoundary_natural (K L : Compacts interiorOpen) (hKL : K ≤ L) (k : ℕ) :
    homologyMap (supportMap (restrictedProjection wholeProjection interiorOpen) V K L hKL) k ≫
      fixedToBoundary V L k = fixedToBoundary V K k := by
  unfold fixedToBoundary
  rw [← Category.assoc,fixedSupportIso_inv_natural,Category.assoc,← homologyMap_comp,
    boundaryRelativeMap_transition]

/-- The actual compact-support comparison is descended from literal fixed-support excision. -/
def compactToBoundary (k : ℕ) :
    compactCohomology (restrictedProjection wholeProjection interiorOpen) V k ⟶
      (ambientRelativeCochains (SymmetricSpaceBordifiedQuotient.boundary principalSix) V).homology k :=
  compactCohomologyDesc (restrictedProjection wholeProjection interiorOpen) V k _
    (fun K => fixedToBoundary V K k) (fun K L hKL => fixedToBoundary_natural V K L hKL k)

/-- The actual compact-support comparison retains its literal fixed-support formula. -/
theorem compactToBoundary_classMap (K : Compacts interiorOpen) (k : ℕ) :
    compactClassMap (restrictedProjection wholeProjection interiorOpen) V K k ≫ compactToBoundary V k =
      fixedToBoundary V K k := compactCohomologyDesc_ι _ _ _ _ _ _ _

end TernaryPoly.CompactInteriorRelativeBoundary
