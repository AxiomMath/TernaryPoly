module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundary

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCoefficient EquivariantSingularSmall
open SingularBoundaryRestriction SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open SymmetricSpaceBordifiedPrincipalSix

variable (V : Rep.{0} ℚ principalSix)

/-- The designated interior is exactly the complement of the actual boundary. -/
theorem interior_eq_boundary_compl : (interiorOpen : Set BordifiedOrbit) = (boundary principalSix)ᶜ := by
  rw [← interiorOpen_compl,compl_compl]

/-- Equal interior supports are identified by literal support enlargement maps in both directions. -/
def interiorComplementSupportIso : supportCochains wholeProjection V interiorOpen ≅
    supportCochains wholeProjection V (boundary principalSix)ᶜ where
  hom := supportMap wholeProjection V _ _ interior_eq_boundary_compl.le
  inv := supportMap wholeProjection V _ _ interior_eq_boundary_compl.symm.le
  hom_inv_id := by rw [supportMap_comp,supportMap_self]
  inv_hom_id := by rw [supportMap_comp,supportMap_self]

/-- The literal complement adapter retains the identical ambient geometric cochain. -/
theorem interiorComplementSupportIso_inclusion :
    (interiorComplementSupportIso V).hom ≫ supportInclusion wholeProjection V (boundary principalSix)ᶜ =
      supportInclusion wholeProjection V interiorOpen :=
  supportMap_inclusion wholeProjection V interiorOpen (boundary principalSix)ᶜ interior_eq_boundary_compl.le

/-- The relative kernel equals the actual kernel of restriction to the double complement
of the boundary, through actual kernel and support maps and the cochain comparison. -/
def boundarySupportIso : relativeCochains V ≅ supportCochains wholeProjection V (boundary principalSix)ᶜ :=
  (boundaryGeometricIso V) ≪≫ (supportAtInteriorIso V).symm ≪≫ interiorComplementSupportIso V

/-- The actual relative-to-support comparison is the identity on ambient cochains under the
equivariant/geometric comparison. -/
theorem boundarySupportIso_inclusion :
    (boundarySupportIso V).hom ≫ supportInclusion wholeProjection V (boundary principalSix)ᶜ =
      relativeInclusion V ≫ (cochainIso wholeProjection wholeQuotientCovering V).hom := by
  have h : (supportAtInteriorIso V).inv ≫ supportInclusion wholeProjection V interiorOpen =
      kernel.ι (geometricBoundaryRestriction V) := by
    rw [← supportAtInteriorIso_inclusion,Iso.inv_hom_id_assoc]
  change ((boundaryGeometricIso V).hom ≫ (supportAtInteriorIso V).inv ≫
    (interiorComplementSupportIso V).hom) ≫ _ = _
  rw [Category.assoc,Category.assoc,interiorComplementSupportIso_inclusion,h,boundaryGeometricIso_inclusion]

/-- Actual restriction from a complementary neighborhood to the full boundary identifies
with literal geometric support enlargement to the complement of that boundary. -/
theorem supportRelativeIso_toBoundarySupport (K : Compacts interiorOpen) :
    (supportRelativeIso (openCompactImage interiorOpen K) V).hom ≫
      supportMap wholeProjection V (openCompactImage interiorOpen K) (boundary principalSix)ᶜ
        ((openCompactImage_subset interiorOpen K).trans interior_eq_boundary_compl.le) =
      boundaryRelativeMap (outsideCompact K) (boundary_subset_outsideCompact K) V ≫
        (ambientBoundaryIso V).hom ≫ (boundarySupportIso V).hom := by
  dsimp only [outsideCompact]
  apply (cancel_mono (supportInclusion wholeProjection V (boundary principalSix)ᶜ)).mp
  rw [Category.assoc,supportMap_inclusion,supportRelativeIso_inclusion]
  rw [Category.assoc,Category.assoc,boundarySupportIso_inclusion]
  rw [← Category.assoc (ambientBoundaryIso V).hom,ambientBoundaryIso_inclusion]
  have h := boundaryRelativeMap_inclusion (outsideCompact K) (boundary_subset_outsideCompact K) V
  exact (congrArg (fun f => f ≫ (cochainIso wholeProjection wholeQuotientCovering V).hom) h).symm.trans
    (Category.assoc _ _ _)

/-- The fixed-stage compact/relative comparison becomes literal support enlargement after
the actual boundary-kernel adapter, with only genuine inverse open excision on the source. -/
theorem fixedToBoundary_toSupport (K : Compacts interiorOpen) (k : ℕ) :
    fixedToBoundary V K k ≫ homologyMap (ambientBoundaryIso V).hom k ≫
      homologyMap (boundarySupportIso V).hom k =
    (openSupportIso wholeProjection V interiorOpen K k).inv ≫ homologyMap
      (supportMap wholeProjection V (openCompactImage interiorOpen K) (boundary principalSix)ᶜ
        ((openCompactImage_subset interiorOpen K).trans interior_eq_boundary_compl.le)) k := by
  have h := congrArg (fun f => homologyMap f k) (supportRelativeIso_toBoundarySupport V K)
  simp only [homologyMap_comp] at h
  erw [homologyMap_comp (boundaryRelativeMap (outsideCompact K) (boundary_subset_outsideCompact K) V)
    ((ambientBoundaryIso V).hom ≫ (boundarySupportIso V).hom) k,
    homologyMap_comp (ambientBoundaryIso V).hom (boundarySupportIso V).hom k] at h
  apply (cancel_epi (fixedSupportIso V K k).hom).mp
  change (fixedSupportIso V K k).hom ≫ ((fixedSupportIso V K k).inv ≫ _) ≫ _ ≫ _ = _
  rw [← Category.assoc,Iso.hom_inv_id_assoc]
  change _ = (homologyMap (supportRelativeIso (openCompactImage interiorOpen K) V).hom k ≫
    (openSupportIso wholeProjection V interiorOpen K k).hom) ≫
      (openSupportIso wholeProjection V interiorOpen K k).inv ≫ _
  rw [Category.assoc,Iso.hom_inv_id_assoc]
  exact h.symm

/-- The actual compact/relative comparison sends each compact-support representative to literal
support enlargement, under the identity-on-ambient boundary support adapter. -/
theorem compactRelativeIso_fixedSupport (K : Compacts interiorOpen) (k : ℕ) :
    compactClassMap (restrictedProjection wholeProjection interiorOpen) V K k ≫
      (interiorCompactIso V k).inv ≫ (compactRelativeIso V k).hom ≫
        homologyMap (boundarySupportIso V).hom k =
    (openSupportIso wholeProjection V interiorOpen K k).inv ≫ homologyMap
      (supportMap wholeProjection V (openCompactImage interiorOpen K) (boundary principalSix)ᶜ
        ((openCompactImage_subset interiorOpen K).trans interior_eq_boundary_compl.le)) k := by
  rw [compactRelativeIso_hom,Category.assoc,Iso.inv_hom_id_assoc]
  rw [← Category.assoc,← Category.assoc,compactToBoundary_classMap,Category.assoc]
  exact fixedToBoundary_toSupport V K k

end TernaryPoly.CompactInteriorRelativeBoundary
