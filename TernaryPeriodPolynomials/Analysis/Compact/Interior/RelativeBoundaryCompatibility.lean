module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryStages
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryBoundary
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Representatives

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCoefficient SingularCoverNaturality EquivariantSingularSmall
open SingularBoundaryRestriction SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence
open SymmetricSpaceBordifiedQuotient SingularLocalCompactDuality

variable (V : Rep.{0} ℚ principalSix)

/-- The literal ambient relative cochain is restricted to the actual open interior. -/
def ambientInteriorMap (W : Set BordifiedOrbit) : ambientRelativeCochains W V ⟶
    localCochains (restrictedProjection wholeProjection interiorOpen) (by exact Fact.out) V :=
  ambientRelativeInclusion W V ≫ (cochainIso wholeProjection wholeQuotientCovering V).hom ≫
    localRestriction wholeProjection interiorOpen V

/-- Genuine fixed-support excision preserves the actual interior cochain. -/
theorem fixedSupportIso_forget (K : Compacts interiorOpen) (k : ℕ) :
    (fixedSupportIso V K k).hom ≫
      homologyMap (supportInclusion (restrictedProjection wholeProjection interiorOpen) V K) k =
        homologyMap (ambientInteriorMap V (outsideCompact K)) k := by
  change (homologyMap (supportRelativeIso (openCompactImage interiorOpen K) V).hom k ≫
    (openSupportIso wholeProjection V interiorOpen K k).hom) ≫ _ = _
  rw [Category.assoc,openSupportIso_forget,← Category.assoc,← homologyMap_comp,
    supportRelativeIso_inclusion]
  rw [← homologyMap_comp]
  exact congrArg (fun f => homologyMap f k) (Category.assoc _ _ _)

/-- The actual boundary-relative map retains its literal ordinary interior restriction. -/
theorem boundaryRelativeMap_toInterior (W : Set BordifiedOrbit)
    (hAW : boundary principalSix ⊆ W) :
    boundaryRelativeMap W hAW V ≫ ambientInteriorMap V (boundary principalSix) =
      ambientInteriorMap V W := by
  unfold ambientInteriorMap
  rw [← Category.assoc,← Category.assoc,boundaryRelativeMap_inclusion,Category.assoc]

/-- Every fixed-support comparison preserves the actual compact-to-ordinary map. -/
theorem fixedToBoundary_forget (K : Compacts interiorOpen) (k : ℕ) :
    fixedToBoundary V K k ≫ homologyMap (ambientInteriorMap V (boundary principalSix)) k =
      homologyMap (supportInclusion (restrictedProjection wholeProjection interiorOpen) V K) k := by
  unfold fixedToBoundary
  rw [Category.assoc,← homologyMap_comp,boundaryRelativeMap_toInterior,
    ← fixedSupportIso_forget,Iso.inv_hom_id_assoc]

/-- The actual descended compact-support comparison preserves literal support-forgetting
and literal restriction of the ambient relative class to the open interior. -/
theorem compactToBoundary_forget (k : ℕ) :
    compactToBoundary V k ≫ homologyMap (ambientInteriorMap V (boundary principalSix)) k =
      compactForget (restrictedProjection wholeProjection interiorOpen) V k := by
  apply compactCohomology_hom_ext
  intro K
  rw [← Category.assoc,compactToBoundary_classMap,fixedToBoundary_forget,compactForget_classMap]

end TernaryPoly.CompactInteriorRelativeBoundary
