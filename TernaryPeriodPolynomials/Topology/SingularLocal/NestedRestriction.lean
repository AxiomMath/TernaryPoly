module

public import TernaryPeriodPolynomials.Topology.Singular.CoverPullbackIso
public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Cochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex SingularLocalCoefficient SingularCoverNaturality
open EquivariantSingularSmall EquivariantSingularMayerVietoris SphereOddDegree

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]

/-- Every literal restriction is again a quotient covering with its canonical restricted action. -/
instance restrictedCoveringFact (D : Set B) :
    Fact (IsQuotientCoveringMap (restrictedProjection p D) G) := ⟨restrictedQuotientCovering p D⟩

/-- The nested covering preimage is invariant under its canonical restricted deck action. -/
instance nestedPreimageInvariantFact (A D : Set B) :
    Fact (InvariantSet G (TopCat.of (p ⁻¹' D))
      ((restrictedProjection p D) ⁻¹' (Subtype.val ⁻¹' A))) :=
  ⟨preimage_invariant (G := G) (restrictedProjection p D) (Subtype.val ⁻¹' A)⟩

/-- The canonical deck action on the nested covering preimage. -/
instance nestedPreimageAction (A D : Set B) :
    MulAction G ((restrictedProjection p D) ⁻¹' (Subtype.val ⁻¹' A)) :=
  invariantSubtypeAction G (TopCat.of (p ⁻¹' D)) _

/-- The nested deck action is continuous. -/
instance nestedPreimageContinuous (A D : Set B) :
    ContinuousConstSMul G ((restrictedProjection p D) ⁻¹' (Subtype.val ⁻¹' A)) :=
  invariantSubtypeContinuous G (TopCat.of (p ⁻¹' D)) _

/-- The literal iterated restriction of the covering. -/
abbrev nestedProjection (A D : Set B) :=
  restrictedProjection (restrictedProjection p D) (Subtype.val ⁻¹' A)

/-- Flattening a nested base subset is a genuine homeomorphism to the intersection. -/
def nestedBaseHomeomorph (A D : Set B) :
    (Subtype.val ⁻¹' A : Set D) ≃ₜ (A ∩ D : Set B) where
  toFun x := ⟨x.val.val,x.property,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Flattening the nested covering preimage is a genuine equivariant homeomorphism. -/
def nestedTotalHomeomorph (A D : Set B) :
    ((restrictedProjection p D) ⁻¹' (Subtype.val ⁻¹' A)) ≃ₜ (p ⁻¹' (A ∩ D)) where
  toFun x := ⟨x.val.val,x.property,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The actual flattening homeomorphisms form a commuting square of quotient coverings. -/
theorem nestedFlatten_square (A D : Set B) :
    (TopCat.isoOfHomeo (nestedTotalHomeomorph p A D)).hom ≫ restrictedProjection p (A ∩ D) =
      nestedProjection p A D ≫ (TopCat.isoOfHomeo (nestedBaseHomeomorph A D)).hom := rfl

/-- Actual pullback along the two flattening homeomorphisms. -/
def nestedCochainMap (A D : Set B) (V : Rep.{0} ℚ G) :
    localCochains (restrictedProjection p (A ∩ D)) (restrictedQuotientCovering p (A ∩ D)) V ⟶
      localCochains (nestedProjection p A D)
        (restrictedQuotientCovering (restrictedProjection p D) (Subtype.val ⁻¹' A)) V :=
  localPullback (nestedProjection p A D) (restrictedProjection p (A ∩ D))
    (TopCat.isoOfHomeo (nestedTotalHomeomorph p A D)).hom
    (TopCat.isoOfHomeo (nestedBaseHomeomorph A D)).hom (nestedFlatten_square p A D)
    (restrictedQuotientCovering (restrictedProjection p D) (Subtype.val ⁻¹' A))
    (restrictedQuotientCovering p (A ∩ D)) (fun _ _ => rfl) V

/-- Equivariant Hom-cochain pullback along flattening is an actual isomorphism. -/
theorem nestedEquivariantCochainMap_isIso (A D : Set B) (V : Rep.{0} ℚ G) :
    IsIso (cochainPullback
      ((TopCat.isoOfHomeo (nestedTotalHomeomorph p A D)).hom :
        TopCat.of ((restrictedProjection p D) ⁻¹' (Subtype.val ⁻¹' A)) ⟶ TopCat.of (p ⁻¹' (A ∩ D)))
      (fun _ _ => rfl) V) := by
  exact cochainPullback_isIso_of_inverse _
    (TopCat.isoOfHomeo (nestedTotalHomeomorph p A D)).inv (fun _ _ => rfl) (fun _ _ => rfl)
    (by rfl) (by rfl) V

/-- Actual pullback along the flattening maps is a cochain isomorphism. -/
instance nestedCochainMap_isIso (A D : Set B) (V : Rep.{0} ℚ G) : IsIso (nestedCochainMap p A D V) := by
  have := nestedEquivariantCochainMap_isIso p A D V
  unfold nestedCochainMap
  apply localPullback_isIso

/-- The flattening maps identify the actual local-cochain complexes of iterated and direct restrictions. -/
def nestedCochainIso (A D : Set B) (V : Rep.{0} ℚ G) :
    localCochains (restrictedProjection p (A ∩ D)) (restrictedQuotientCovering p (A ∩ D)) V ≅
      localCochains (nestedProjection p A D)
        (restrictedQuotientCovering (restrictedProjection p D) (Subtype.val ⁻¹' A)) V :=
  asIso (nestedCochainMap p A D V)

/-- The actual flattening comparison retains restriction from the containing subspace. -/
theorem nestedCochainIso_restriction (A D : Set B) (V : Rep.{0} ℚ G) :
    nestedLocalRestriction p (A ∩ D) D Set.inter_subset_right V ≫ (nestedCochainIso p A D V).hom =
      localRestriction (restrictedProjection p D) (Subtype.val ⁻¹' A) V := by
  change nestedLocalRestriction p (A ∩ D) D Set.inter_subset_right V ≫ nestedCochainMap p A D V = _
  unfold nestedLocalRestriction nestedCochainMap
  erw [← localPullback_comp]
  rfl

end TernaryPoly.SingularLocalSupport
