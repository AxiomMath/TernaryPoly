module

public import TernaryPeriodPolynomials.Topology.SingularLocal.NestedRestriction

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory HomologicalComplex SingularLocalCoefficient SingularCoverNaturality
open EquivariantSingularSmall SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]

/-- The literal flattening homeomorphism for a subset already contained in the containing subspace. -/
def includedBaseHomeomorph (A D : Set B) (hAD : A ⊆ D) : (Subtype.val ⁻¹' A : Set D) ≃ₜ A where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,hAD x.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The literal equivariant flattening of the covering preimages for a contained subset. -/
def includedTotalHomeomorph (A D : Set B) (hAD : A ⊆ D) :
    ((restrictedProjection p D) ⁻¹' (Subtype.val ⁻¹' A)) ≃ₜ (p ⁻¹' A) where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,hAD x.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The contained-subset flattening maps commute with the actual quotient-covering maps. -/
theorem includedFlatten_square (A D : Set B) (hAD : A ⊆ D) :
    (TopCat.isoOfHomeo (includedTotalHomeomorph p A D hAD)).hom ≫ restrictedProjection p A =
      nestedProjection p A D ≫ (TopCat.isoOfHomeo (includedBaseHomeomorph A D hAD)).hom := rfl

/-- Actual cochain pullback identifies direct and iterated restrictions to a contained subset. -/
def includedCochainMap (A D : Set B) (hAD : A ⊆ D) (V : Rep.{0} ℚ G) :
    localCochains (restrictedProjection p A) (restrictedQuotientCovering p A) V ⟶
      localCochains (nestedProjection p A D)
        (restrictedQuotientCovering (restrictedProjection p D) (Subtype.val ⁻¹' A)) V :=
  localPullback (nestedProjection p A D) (restrictedProjection p A)
    (TopCat.isoOfHomeo (includedTotalHomeomorph p A D hAD)).hom
    (TopCat.isoOfHomeo (includedBaseHomeomorph A D hAD)).hom (includedFlatten_square p A D hAD)
    (restrictedQuotientCovering (restrictedProjection p D) (Subtype.val ⁻¹' A))
    (restrictedQuotientCovering p A) (fun _ _ => rfl) V

/-- The actual contained-subset pullback is an isomorphism of cochain complexes. -/
instance includedCochainMap_isIso (A D : Set B) (hAD : A ⊆ D) (V : Rep.{0} ℚ G) :
    IsIso (includedCochainMap p A D hAD V) := by
  have := cochainPullback_isIso_of_inverse
    ((TopCat.isoOfHomeo (includedTotalHomeomorph p A D hAD)).hom :
      TopCat.of ((restrictedProjection p D) ⁻¹' (Subtype.val ⁻¹' A)) ⟶ TopCat.of (p ⁻¹' A))
    (TopCat.isoOfHomeo (includedTotalHomeomorph p A D hAD)).inv (fun _ _ => rfl) (fun _ _ => rfl)
    (by rfl) (by rfl) V
  unfold includedCochainMap
  apply localPullback_isIso

/-- The actual contained-subset cochain isomorphism, with literal pullback as its forward map. -/
def includedCochainIso (A D : Set B) (hAD : A ⊆ D) (V : Rep.{0} ℚ G) :=
  asIso (includedCochainMap p A D hAD V)

/-- The contained-subset comparison preserves the actual restriction from the containing subspace. -/
theorem includedCochainIso_restriction (A D : Set B) (hAD : A ⊆ D) (V : Rep.{0} ℚ G) :
    nestedLocalRestriction p A D hAD V ≫ (includedCochainIso p A D hAD V).hom =
      localRestriction (restrictedProjection p D) (Subtype.val ⁻¹' A) V := by
  change nestedLocalRestriction p A D hAD V ≫ includedCochainMap p A D hAD V = _
  unfold nestedLocalRestriction includedCochainMap
  erw [← localPullback_comp]
  rfl

/-- Actual ambient restriction is compatible with direct and iterated restriction to a contained subset. -/
theorem includedCochainIso_ambient (A D : Set B) (hAD : A ⊆ D) (V : Rep.{0} ℚ G) :
    localRestriction p D V ≫ localRestriction (restrictedProjection p D) (Subtype.val ⁻¹' A) V =
      localRestriction p A V ≫ (includedCochainIso p A D hAD V).hom := by
  rw [← includedCochainIso_restriction,← Category.assoc,localRestriction_nested]

end TernaryPoly.SingularLocalCompactMV
