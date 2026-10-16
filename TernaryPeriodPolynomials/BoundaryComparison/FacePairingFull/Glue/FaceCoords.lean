module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.GeoFace
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.InnerLift

@[expose] public section


/-!
# Intrinsic face coordinates of the lifts

The face coordinates (line, plane) of a class of `H²(∂M; W)` are the line and plane components `homPullback coneLine`,
`homPullback conePlane` of the model cone (the model's restriction to the open faces; for restrictions of global classes these
are the maps of `boundary_coordinates_are_face_restrictions` and, through `singular_restriction_eq_geoRestriction`, the library's
restrictions to the faces) of the class under `(modelBoundary_cohomology_iso W 2).inv`.

For the comparison `Ψ` of the face-wise glue (carried, hence canonical, `CanonFull`) the boundary cocycles of the glue have the
face coordinates of the inner lifts of `InnerLift`: `(b, 0)` for the line lifts (`lineLift_faceCoords`), `(0, ξ)` for the plane
lifts (`planeLift_faceCoords`), and for the `φ`-twisted dual lifts the complementary face coordinate vanishes
(`lineLiftA_faceCoords`, `planeLiftA_faceCoords`).  Together with `coneLiftGeo` (`GeoFace`), which defines the lifts through the
lifts of `InnerLift` alone, this restates the glue without `Ψ`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane
open TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient)
open TernaryPoly.EquivariantSingularResolution

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

section FaceCoordinates

open HomologicalComplex TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.SingularBoundaryRestriction TernaryPoly.SymmetricSpaceBoundaryGeometricCone
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SingularLocalCompactCap.Algebra

/-- The line face coordinate of a class of `H²(∂M; W)`: its image under `(modelBoundary_cohomology_iso W 2).inv` followed by
the line component `homPullback coneLine` of the cone (the model's restriction to the open line faces). -/
def faceLineCoord (W : Rep.{0} ℚ principalSix) (x : (localBoundaryCochains W).homology 2) :
    (homCochains (TopHomology.prodComplex Γ6 RationalGL3 (TernaryPoly.OrdinaryIncidence.Line)) W).homology 2 :=
  (homologyMap (homPullback coneLine W) 2).hom ((modelBoundary_cohomology_iso W 2).inv.hom x)

/-- The plane face coordinate of a class of `H²(∂M; W)`. -/
def facePlaneCoord (W : Rep.{0} ℚ principalSix) (x : (localBoundaryCochains W).homology 2) :
    (homCochains (TopHomology.prodComplex Γ6 RationalGL3 (TernaryPoly.OrdinaryIncidence.Plane)) W).homology 2 :=
  (homologyMap (homPullback conePlane W) 2).hom ((modelBoundary_cohomology_iso W 2).inv.hom x)

variable {n : ℕ}

/-- **Intrinsic coordinates of the line lift.**  A boundary cocycle `β` which pulls back along a carried `Ψ` to the cone lift
`lineLiftB z w` (cohomologous) has face coordinates `(b, 0)`: its line coordinate is the class of the line cocycle `z` and its
plane coordinate is `0`. -/
theorem lineLift_faceCoords {Ψ : coneR ⟶ boundaryChains} (hΨ : IsCarriedPsi Ψ)
    {z : MaximalCycles n trivialCharacter .line} {w : EdgeCochains n trivialCharacter 1} (hw : EdgePrimitive z w)
    (β : boundaryChains.X 2 ⟶ coeffRep (rationalCoefficientComponent n trivialCharacter))
    (hβ : boundaryChains.d (2 + 1) 2 ≫ β = 0) (η : coneR.X 1 ⟶ coeffRep (rationalCoefficientComponent n trivialCharacter))
    (hη : Ψ.f 2 ≫ β = lineLiftB z w + coneR.d 2 1 ≫ η) :
    faceLineCoord _ (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 β hβ)) =
      modelCls (rationalCoefficientComponent n trivialCharacter) psiLine psiLine_smul
        ⟨restrictN6 (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z.val,
          restrictN6_cocycle _ z.val z.property⟩ ∧
    facePlaneCoord _ (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 β hβ)) = 0 := by
  have hcl := cochainClass_eq_isoHom hΨ _ (lineLiftB_cocycle hw) β hβ η hη
  have hu : ∀ x e, (restrictN6 (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z.val).1 x
      (endpoint .line e) = (differentialOne N6 (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges)
        (restrictN6 (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges) w)).1 x e :=
    fun x e => hw x e
  have key : (modelBoundary_cohomology_iso _ 2).inv.hom
      (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 β hβ)) =
      innerLineCone (rationalCoefficientComponent n trivialCharacter)
        ⟨restrictN6 (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z.val,
          restrictN6_cocycle _ z.val z.property⟩
        (restrictN6 (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges) w) hu := by
    rw [hcl]
    exact (modelBoundary_cohomology_iso _ 2).hom_inv_id_apply _
  unfold faceLineCoord facePlaneCoord
  rw [key]
  exact ⟨innerLineCone_line _ _ _ hu, innerLineCone_plane _ _ _ hu⟩

/-- The plane lift has face coordinates `(0, ξ)`. -/
theorem planeLift_faceCoords {Ψ : coneR ⟶ boundaryChains} (hΨ : IsCarriedPsi Ψ)
    {z : MaximalCycles n trivialCharacter .plane} {w : EdgeCochains n trivialCharacter 1} (hw : EdgePrimitiveP z w)
    (β : boundaryChains.X 2 ⟶ coeffRep (rationalCoefficientComponent n trivialCharacter))
    (hβ : boundaryChains.d (2 + 1) 2 ≫ β = 0) (η : coneR.X 1 ⟶ coeffRep (rationalCoefficientComponent n trivialCharacter))
    (hη : Ψ.f 2 ≫ β = planeLiftB z w + coneR.d 2 1 ≫ η) :
    facePlaneCoord _ (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 β hβ)) =
      modelCls (rationalCoefficientComponent n trivialCharacter) psiPlane psiPlane_smul
        ⟨restrictN6 (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z.val,
          restrictN6_cocycle _ z.val z.property⟩ ∧
    faceLineCoord _ (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 β hβ)) = 0 := by
  have hcl := cochainClass_eq_isoHom hΨ _ (planeLiftB_cocycle hw) β hβ η hη
  have hu : ∀ x e, (restrictN6 (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z.val).1 x
      (endpoint .plane e) = (differentialOne N6 (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges)
        (restrictN6 (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges) w)).1 x e :=
    fun x e => hw x e
  have key : (modelBoundary_cohomology_iso _ 2).inv.hom
      (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 β hβ)) =
      innerPlaneCone (rationalCoefficientComponent n trivialCharacter)
        ⟨restrictN6 (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z.val,
          restrictN6_cocycle _ z.val z.property⟩
        (restrictN6 (functionRepresentation (rationalCoefficientComponent n trivialCharacter) Edges) w) hu := by
    rw [hcl]
    exact (modelBoundary_cohomology_iso _ 2).hom_inv_id_apply _
  unfold faceLineCoord facePlaneCoord
  rw [key]
  exact ⟨innerPlaneCone_plane _ _ _ hu, innerPlaneCone_line _ _ _ hu⟩

theorem homPullback_coneLine_innerLineCochain {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V]
    [IsScalarTower ℚ ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (z : cochains N6 (functionRepresentation ρ (Flags .line)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    (homPullback coneLine (coeffRep ρ)).f 2 (innerLineCochain ρ z u) =
      modelHomOf ρ psiLine psiLine_smul z := by
  have h := TernaryPoly.SymmetricSpaceBoundaryFull.signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerLineCochain ρ z u)
  have hc : TernaryPoly.SymmetricSpaceBoundaryFull.signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerLineCochain ρ z u) =
      (modelHomOf ρ psiEdge psiEdge_smul u, (modelHomOf ρ psiLine psiLine_smul z, 0)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun t => t.2.1) h).symm

theorem homPullback_conePlane_innerLineCochain {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V]
    [IsScalarTower ℚ ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (z : cochains N6 (functionRepresentation ρ (Flags .line)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    (homPullback conePlane (coeffRep ρ)).f 2 (innerLineCochain ρ z u) = 0 := by
  have h := TernaryPoly.SymmetricSpaceBoundaryFull.signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerLineCochain ρ z u)
  have hc : TernaryPoly.SymmetricSpaceBoundaryFull.signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerLineCochain ρ z u) =
      (modelHomOf ρ psiEdge psiEdge_smul u, (modelHomOf ρ psiLine psiLine_smul z, 0)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun t => t.2.2) h).symm

theorem homPullback_coneLine_innerPlaneCochain {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V]
    [IsScalarTower ℚ ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (z : cochains N6 (functionRepresentation ρ (Flags .plane)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    (homPullback coneLine (coeffRep ρ)).f 2 (innerPlaneCochain ρ z u) = 0 := by
  have h := TernaryPoly.SymmetricSpaceBoundaryFull.signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
    (innerPlaneCochain ρ z u)
  have hc : TernaryPoly.SymmetricSpaceBoundaryFull.signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerPlaneCochain ρ z u) =
      (-modelHomOf ρ psiEdge psiEdge_smul u, (0, modelHomOf ρ psiPlane psiPlane_smul z)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun t => t.2.1) h).symm

theorem homPullback_conePlane_innerPlaneCochain {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V]
    [IsScalarTower ℚ ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (z : cochains N6 (functionRepresentation ρ (Flags .plane)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    (homPullback conePlane (coeffRep ρ)).f 2 (innerPlaneCochain ρ z u) = modelHomOf ρ psiPlane psiPlane_smul z := by
  have h := TernaryPoly.SymmetricSpaceBoundaryFull.signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
    (innerPlaneCochain ρ z u)
  have hc : TernaryPoly.SymmetricSpaceBoundaryFull.signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerPlaneCochain ρ z u) =
      (-modelHomOf ρ psiEdge psiEdge_smul u, (0, modelHomOf ρ psiPlane psiPlane_smul z)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun t => t.2.2) h).symm

/-- **Face coordinates of the dual plane lift**: plane coordinate the class of the paired twisted line cocycle, line
coordinate `0`. -/
theorem planeLiftA_faceCoords {Ψ : coneR ⟶ boundaryChains} (hΨ : IsCarriedPsi Ψ) (T : DualityDataP n trivialCharacter)
    (r : ℂ →ₗ[ℚ] ℚ) {y : MaximalCycles n trivialCharacter .line} {s : EdgeCochains n trivialCharacter 1}
    (hs : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e)
    (α : boundaryChains.X 2 ⟶ TernaryPoly.SingularLocalDuality.dualRepresentation
      (coeffRep (rationalCoefficientComponent n trivialCharacter)))
    (hα : boundaryChains.d (2 + 1) 2 ≫ α = 0)
    (η : coneR.X 1 ⟶ TernaryPoly.SingularLocalDuality.dualRepresentation
      (coeffRep (rationalCoefficientComponent n trivialCharacter)))
    (hη : Ψ.f 2 ≫ α = planeLiftA T r y s + coneR.d 2 1 ≫ η) :
    faceLineCoord _ (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 α hα)) = 0 ∧
    ∃ hcoc : (((homCochains (TopHomology.prodComplex Γ6 RationalGL3 (TernaryPoly.OrdinaryIncidence.Plane))
      (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).d 2 3).hom
      (modelHomOf (twistRepP T) psiPlane psiPlane_smul (twistCochain2P T y.val) ≫ pairHomP T r) = 0),
      facePlaneCoord _ (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 α hα)) =
      cls2 (homCochains (TopHomology.prodComplex Γ6 RationalGL3 (TernaryPoly.OrdinaryIncidence.Plane))
        (TernaryPoly.SingularLocalDuality.dualRepresentation
          (coeffRep (rationalCoefficientComponent n trivialCharacter))))
        (modelHomOf (twistRepP T) psiPlane psiPlane_smul (twistCochain2P T y.val) ≫ pairHomP T r) hcoc := by
  have hA := planeLiftA_cocycle T r hs
  have hcl := cochainClass_eq_isoHom hΨ _ hA α hα η hη
  have key : (modelBoundary_cohomology_iso _ 2).inv.hom
      (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 α hα)) =
      cls2 (homCochains coneR _) (planeLiftA T r y s) hA := by
    rw [hcl]
    exact (modelBoundary_cohomology_iso _ 2).hom_inv_id_apply _
  have hL : ((homCochains _ _).d 2 3).hom ((homPullback coneLine
      (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).f 2 (planeLiftA T r y s)) = 0 :=
    map_cocycle _ (homPullback coneLine _) _ hA
  have hP : ((homCochains _ _).d 2 3).hom ((homPullback conePlane
      (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).f 2 (planeLiftA T r y s)) = 0 :=
    map_cocycle _ (homPullback conePlane _) _ hA
  have e1 : (homPullback conePlane (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).f 2 (planeLiftA T r y s) =
      modelHomOf (twistRepP T) psiPlane psiPlane_smul (twistCochain2P T y.val) ≫ pairHomP T r := by
    have h := homPullback_conePlane_innerPlaneCochain (twistRepP T) (twistCochain2P T y.val) (twistCochain1P T s)
    change conePlane.f 2 ≫ (innerPlaneCochain (twistRepP T) (twistCochain2P T y.val) (twistCochain1P T s) ≫ pairHomP T r) = _
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ pairHomP T r) h)
  have e2 : (homPullback coneLine (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).f 2 (planeLiftA T r y s) = 0 := by
    have h := homPullback_coneLine_innerPlaneCochain (twistRepP T) (twistCochain2P T y.val) (twistCochain1P T s)
    change coneLine.f 2 ≫ (innerPlaneCochain (twistRepP T) (twistCochain2P T y.val) (twistCochain1P T s) ≫ pairHomP T r) = _
    exact ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ pairHomP T r) h)).trans (zero_comp)
  have hcoc : ((homCochains (TopHomology.prodComplex Γ6 RationalGL3 (TernaryPoly.OrdinaryIncidence.Plane))
      (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).d 2 3).hom
      (modelHomOf (twistRepP T) psiPlane psiPlane_smul (twistCochain2P T y.val) ≫ pairHomP T r) = 0 := by
    rw [← e1]; exact hP
  unfold faceLineCoord facePlaneCoord
  rw [key]
  refine ⟨?_, hcoc, ?_⟩
  · rw [cls2_map _ (homPullback coneLine _) _ hA hL]
    exact (cls2_congr _ hL (map_zero _) e2).trans (cls2_zero _ (map_zero _))
  · rw [cls2_map _ (homPullback conePlane _) _ hA hP]
    exact cls2_congr _ hP hcoc e1

/-- **Face coordinates of the dual line lift**: a boundary cocycle `α` with values in `E^∨` which pulls back to the
`φ`-twisted line-supported lift `lineLiftA T r y s` has plane coordinate `0` and line coordinate the class of the (paired)
twisted line cocycle. -/
theorem lineLiftA_faceCoords {Ψ : coneR ⟶ boundaryChains} (hΨ : IsCarriedPsi Ψ) (T : DualityData n trivialCharacter)
    (r : ℂ →ₗ[ℚ] ℚ) {y : MaximalCycles n trivialCharacter .plane} {s : EdgeCochains n trivialCharacter 1}
    (hs : ∀ x e, y.val.val x (endpoint .plane e) = differentialOneRaw s.val x e)
    (α : boundaryChains.X 2 ⟶ TernaryPoly.SingularLocalDuality.dualRepresentation
      (coeffRep (rationalCoefficientComponent n trivialCharacter)))
    (hα : boundaryChains.d (2 + 1) 2 ≫ α = 0)
    (η : coneR.X 1 ⟶ TernaryPoly.SingularLocalDuality.dualRepresentation
      (coeffRep (rationalCoefficientComponent n trivialCharacter)))
    (hη : Ψ.f 2 ≫ α = lineLiftA T r y s + coneR.d 2 1 ≫ η) :
    facePlaneCoord _ (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 α hα)) = 0 ∧
    ∃ hcoc : (((homCochains (TopHomology.prodComplex Γ6 RationalGL3 (TernaryPoly.OrdinaryIncidence.Line)) (TernaryPoly.SingularLocalDuality.dualRepresentation (coeffRep (rationalCoefficientComponent n trivialCharacter)))).d 2 3).hom (modelHomOf (twistRep T) psiLine psiLine_smul (twistCochain2 T y.val) ≫ pairHom T r) = 0), faceLineCoord _ (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 α hα)) =
      cls2 (homCochains (TopHomology.prodComplex Γ6 RationalGL3 (TernaryPoly.OrdinaryIncidence.Line))
        (TernaryPoly.SingularLocalDuality.dualRepresentation
          (coeffRep (rationalCoefficientComponent n trivialCharacter))))
        (modelHomOf (twistRep T) psiLine psiLine_smul (twistCochain2 T y.val) ≫ pairHom T r) hcoc := by
  have hA := lineLiftA_cocycle T r hs
  have hcl := cochainClass_eq_isoHom hΨ _ hA α hα η hη
  have key : (modelBoundary_cohomology_iso _ 2).inv.hom
      (cochainClass _ 2 (cocycleOf boundaryProjection _ 2 α hα)) =
      cls2 (homCochains coneR _) (lineLiftA T r y s) hA := by
    rw [hcl]
    exact (modelBoundary_cohomology_iso _ 2).hom_inv_id_apply _
  have hL : ((homCochains _ _).d 2 3).hom ((homPullback coneLine
      (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).f 2 (lineLiftA T r y s)) = 0 :=
    map_cocycle _ (homPullback coneLine _) _ hA
  have hP : ((homCochains _ _).d 2 3).hom ((homPullback conePlane
      (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).f 2 (lineLiftA T r y s)) = 0 :=
    map_cocycle _ (homPullback conePlane _) _ hA
  have e1 : (homPullback coneLine (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).f 2 (lineLiftA T r y s) =
      modelHomOf (twistRep T) psiLine psiLine_smul (twistCochain2 T y.val) ≫ pairHom T r := by
    have h := homPullback_coneLine_innerLineCochain (twistRep T) (twistCochain2 T y.val) (twistCochain1 T s)
    change coneLine.f 2 ≫ (innerLineCochain (twistRep T) (twistCochain2 T y.val) (twistCochain1 T s) ≫ pairHom T r) = _
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ pairHom T r) h)
  have e2 : (homPullback conePlane (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).f 2 (lineLiftA T r y s) = 0 := by
    have h := homPullback_conePlane_innerLineCochain (twistRep T) (twistCochain2 T y.val) (twistCochain1 T s)
    change conePlane.f 2 ≫ (innerLineCochain (twistRep T) (twistCochain2 T y.val) (twistCochain1 T s) ≫ pairHom T r) = _
    exact ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ pairHom T r) h)).trans (zero_comp)
  unfold faceLineCoord facePlaneCoord
  rw [key]
  have hcoc : ((homCochains (TopHomology.prodComplex Γ6 RationalGL3 (TernaryPoly.OrdinaryIncidence.Line))
      (TernaryPoly.SingularLocalDuality.dualRepresentation
        (coeffRep (rationalCoefficientComponent n trivialCharacter)))).d 2 3).hom
      (modelHomOf (twistRep T) psiLine psiLine_smul (twistCochain2 T y.val) ≫ pairHom T r) = 0 := by
    rw [← e1]; exact hL
  refine ⟨?_, hcoc, ?_⟩
  · rw [cls2_map _ (homPullback conePlane _) _ hA hP]
    exact (cls2_congr _ hP (map_zero _) e2).trans (cls2_zero _ (map_zero _))
  · rw [cls2_map _ (homPullback coneLine _) _ hA hL]
    exact cls2_congr _ hL hcoc e1

end FaceCoordinates

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
