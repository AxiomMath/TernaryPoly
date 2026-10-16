module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoordinateCover
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarCoverSupport

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set SymmetricSpaceCovering
open EquivariantSingularSmall SingularLocalCoefficient

/-- The exact lifted preimage is invariant under the actual deck action. -/
instance coordinatePreimageInvariantFact (U : Set OrbitSpace) :
    Fact (EquivariantSingularSmall.InvariantSet DeckGroup (TopCat.of (CoverOpen univ)) (coverProjection univ ⁻¹' U)) :=
  preimageInvariantFact (coverProjection univ) U

/-- The canonical actual restricted action on the lifted preimage. -/
instance coordinatePreimageAction (U : Set OrbitSpace) : MulAction DeckGroup (coverProjection univ ⁻¹' U) :=
  invariantSubtypeAction DeckGroup (TopCat.of (CoverOpen univ)) (coverProjection univ ⁻¹' U)

/-- Continuity of the canonical restricted deck action. -/
instance coordinatePreimageContinuous (U : Set OrbitSpace) :
    ContinuousConstSMul DeckGroup (coverProjection univ ⁻¹' U) :=
  invariantSubtypeContinuous DeckGroup (TopCat.of (CoverOpen univ)) (coverProjection univ ⁻¹' U)

/-- Every actual lifted domain is literally the corresponding restricted covering total space. -/
def coordinateRestrictionHomeomorph (U : Set OrbitSpace) :
    CoverOpen U ≃ₜ (coverProjection univ ⁻¹' U) where
  toFun x := ⟨⟨x.val, x.property.1, mem_univ _⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property.1, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The actual restricted total-space homeomorphism is equivariant. -/
theorem coordinateRestrictionHomeomorph_equivariant (U : Set OrbitSpace) (g : DeckGroup) (x : CoverOpen U) :
    coordinateRestrictionHomeomorph U (g • x) = g • coordinateRestrictionHomeomorph U x := rfl

/-- The actual inverse restricted total-space homeomorphism is equivariant. -/
theorem coordinateRestrictionHomeomorph_symm_equivariant (U : Set OrbitSpace) (g : DeckGroup)
    (x : (coverProjection univ ⁻¹' U)) :
    (coordinateRestrictionHomeomorph U).symm (g • x) = g • (coordinateRestrictionHomeomorph U).symm x := rfl

/-- The literal pullback along the actual restricted covering homeomorphism. -/
def coordinateRestrictionCochainMap (A : Rep.{0} ℚ DeckGroup) (U : Set OrbitSpace) :
    EquivariantSingularCohomology.cochains DeckGroup (TopCat.of (coverProjection univ ⁻¹' U)) A ⟶
      rationalCoverCochains A U :=
  SingularCoverNaturality.cochainPullback
    (TopCat.isoOfHomeo (X := TopCat.of (CoverOpen U)) (Y := TopCat.of (coverProjection univ ⁻¹' U))
      (coordinateRestrictionHomeomorph U)).hom (coordinateRestrictionHomeomorph_equivariant U) A

/-- The actual restricted singular pullback is an isomorphism. -/
instance coordinateRestrictionCochainMap_isIso (A : Rep.{0} ℚ DeckGroup) (U : Set OrbitSpace) :
    IsIso (coordinateRestrictionCochainMap A U) := by
  let e : TopCat.of (CoverOpen U) ≅ TopCat.of (coverProjection univ ⁻¹' U) :=
    TopCat.isoOfHomeo (coordinateRestrictionHomeomorph U)
  exact SingularCoverNaturality.cochainPullback_isIso_of_inverse e.hom e.inv
    (coordinateRestrictionHomeomorph_equivariant U) (coordinateRestrictionHomeomorph_symm_equivariant U)
    e.hom_inv_id e.inv_hom_id A

/-- The actual restricted singular-cochain homeomorphism isomorphism. -/
def coordinateRestrictionCochainIso (A : Rep.{0} ℚ DeckGroup) (U : Set OrbitSpace) :
    EquivariantSingularCohomology.cochains DeckGroup (TopCat.of (coverProjection univ ⁻¹' U)) A ≅
      rationalCoverCochains A U := asIso (coordinateRestrictionCochainMap A U)

/-- The rational coordinate Hom complex identifies with the actual vertex-fiber local
cochain complex on every genuine restricted covering. -/
def rationalCoverLocalIso (A : Rep.{0} ℚ DeckGroup) (U : Set OrbitSpace) :
    rationalCoverCochains A U ≅
      localCochains (restrictedProjection (coverProjection univ) U)
        (restrictedQuotientCovering (coverProjection univ) U) A :=
  (coordinateRestrictionCochainIso A U).symm ≪≫
    cochainIso _ (restrictedQuotientCovering (coverProjection univ) U) A

/-- The ordinary coordinate Hom complex identifies with the actual local coefficient complex. -/
def rationalCoverGlobalLocalIso (A : Rep.{0} ℚ DeckGroup) :
    rationalCoverCochains A univ ≅ localCochains (coverProjection univ) coordinateCover_quotientCovering A :=
  cochainIso (coverProjection univ) coordinateCover_quotientCovering A

/-- The actual nested-subtype restriction agrees with literal coordinate restriction. -/
theorem coordinateRestrictionCochainIso_inclusion (A : Rep.{0} ℚ DeckGroup) (U : Set OrbitSpace) :
    SingularCoverNaturality.cochainPullback (SphereOddDegree.sInclusion (X := TopCat.of (CoverOpen univ)) (coverProjection univ ⁻¹' U))
        (fun _ _ => rfl) A ≫ (coordinateRestrictionCochainIso A U).hom =
      rationalCoverRestriction A (subset_univ U) := by
  have h := (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map_comp
    (TopCat.isoOfHomeo (X := TopCat.of (CoverOpen U)) (Y := TopCat.of (coverProjection univ ⁻¹' U))
      (coordinateRestrictionHomeomorph U)).hom
    (SphereOddDegree.sInclusion (X := TopCat.of (CoverOpen univ)) (coverProjection univ ⁻¹' U)))
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (congrArg (fun k => c.hom ((k.f n).hom x)) h).symm

/-- The literal coordinate-to-local comparison preserves actual restriction to every quotient subset. -/
theorem rationalCoverLocalIso_restriction (A : Rep.{0} ℚ DeckGroup) (U : Set OrbitSpace) :
    rationalCoverRestriction A (subset_univ U) ≫ (rationalCoverLocalIso A U).hom =
      (rationalCoverGlobalLocalIso A).hom ≫ localRestriction (coverProjection univ) U A := by
  rw [← coordinateRestrictionCochainIso_inclusion, rationalCoverLocalIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have h := SingularCoverNaturality.cochainIso_pullback (G := DeckGroup)
    (restrictedProjection (coverProjection univ) U) (coverProjection univ)
    (SphereOddDegree.sInclusion (X := TopCat.of (CoverOpen univ)) (coverProjection univ ⁻¹' U)) (SphereOddDegree.sInclusion (X := TopCat.of OrbitSpace) U)
    (restricted_square (coverProjection univ) U) (restrictedQuotientCovering (coverProjection univ) U)
    coordinateCover_quotientCovering (fun _ _ => rfl) A
  apply HomologicalComplex.hom_ext
  intro n
  exact congrArg (fun k => k.f n) h

end TernaryPoly.SmoothSingularGlobal
