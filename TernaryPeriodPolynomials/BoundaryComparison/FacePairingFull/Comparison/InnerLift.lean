module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Restriction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Corner

@[expose] public section


/-!
# Inner classes lift to the cohomology of the boundary cone

A stratum cocycle `z` of the cochain model whose pullback to complete flags is the coboundary of an edge
one-cochain `u` (the defining property of an *inner* class, `InnerBoundary`) is the line (resp. plane)
component of a cocycle of the signed cone `coneR`:

* `innerLineCocycle`: the cone cochain `(e, l, 0)` with `l` the Hom cochain of `z` and `e` that of `u`;
* `innerPlaneCocycle`: the cone cochain `(e, 0, p)` with `p` the Hom cochain of `z` and `e` that of `-u`.

Their cohomology classes `innerLineCone`, `innerPlaneCone` have line, resp. plane, component the class of
`z` and the other face component zero.  The corner component of the lift is the Hom cochain of the edge
primitive: this is the cellular form of "the class is zero on every complete flag", and is where the cone
differs from the direct sum of the open faces.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.EquivariantSingularSmall
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- If a line-stratum cochain `z` restricts on complete flags to the coboundary of `u`, the Hom cochain
of `z` pulled back along the flag-to-line incidence is the coboundary of the Hom cochain of `u`. -/
theorem flagLine_comp_modelHomOf (z : cochains N6 (functionRepresentation ρ (Flags .line)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.1 x (endpoint .line e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    flagLineHom.hom.f 2 ≫ modelHomOf ρ psiLine psiLine_smul z =
      (prodComplex Γ6 RationalGL3 Flag).d 2 1 ≫ modelHomOf ρ psiEdge psiEdge_smul u := by
  apply homFunA_injective
  funext y
  obtain ⟨x, φ⟩ := y
  rw [modelHomOf_differentialOne ρ psiEdge psiEdge_smul u]
  have h := homFunA_comp_map (A := coeffRep ρ) (V := RationalGL3) (Γ := Γ6) (Z := Flag)
    (Z' := Line) TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine
    TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant
    (modelHomOf ρ psiLine psiLine_smul z) x φ
  refine h.trans ?_
  rw [homFunA_modelHomOf]
  change z.1 x (psiLine.symm (TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine φ)) =
    (differentialOne N6 (functionRepresentation ρ Edges) u).1 x (psiEdge.symm φ)
  rw [← hu x (psiEdge.symm φ)]
  refine congrArg (z.1 x) ?_
  rw [Equiv.symm_apply_eq]
  have := psiEdge_line (psiEdge.symm φ)
  rw [Equiv.apply_symm_apply] at this
  exact this

/-- The plane analogue of `flagLine_comp_modelHomOf`. -/
theorem flagPlane_comp_modelHomOf (z : cochains N6 (functionRepresentation ρ (Flags .plane)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.1 x (endpoint .plane e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    flagPlaneHom.hom.f 2 ≫ modelHomOf ρ psiPlane psiPlane_smul z =
      (prodComplex Γ6 RationalGL3 Flag).d 2 1 ≫ modelHomOf ρ psiEdge psiEdge_smul u := by
  apply homFunA_injective
  funext y
  obtain ⟨x, φ⟩ := y
  rw [modelHomOf_differentialOne ρ psiEdge psiEdge_smul u]
  have h := homFunA_comp_map (A := coeffRep ρ) (V := RationalGL3) (Γ := Γ6) (Z := Flag)
    (Z' := Plane) TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane
    TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant
    (modelHomOf ρ psiPlane psiPlane_smul z) x φ
  refine h.trans ?_
  rw [homFunA_modelHomOf]
  change z.1 x (psiPlane.symm (TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane φ)) =
    (differentialOne N6 (functionRepresentation ρ Edges) u).1 x (psiEdge.symm φ)
  rw [← hu x (psiEdge.symm φ)]
  refine congrArg (z.1 x) ?_
  rw [Equiv.symm_apply_eq]
  have := psiEdge_plane (psiEdge.symm φ)
  rw [Equiv.apply_symm_apply] at this
  exact this

/-- The cone cochain `(e, l, 0)` attached to an inner line cocycle `z` with edge primitive `u`. -/
def innerLineCochain (z : cochains N6 (functionRepresentation ρ (Flags .line)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    coneR.X 2 ⟶ coeffRep ρ :=
  (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1).symm
    (modelHomOf ρ psiEdge psiEdge_smul u, (modelHomOf ρ psiLine psiLine_smul z, 0))

/-- The cone cochain `(e, 0, p)` attached to an inner plane cocycle `z` with edge primitive `u`. -/
def innerPlaneCochain (z : cochains N6 (functionRepresentation ρ (Flags .plane)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    coneR.X 2 ⟶ coeffRep ρ :=
  (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1).symm
    (-modelHomOf ρ psiEdge psiEdge_smul u, (0, modelHomOf ρ psiPlane psiPlane_smul z))

theorem innerLineCochain_cocycle (z : cocycles N6 (functionRepresentation ρ (Flags .line)))
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.val.1 x (endpoint .line e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    coneR.d 3 2 ≫ innerLineCochain ρ z.val u = 0 := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 2).injective
  rw [cone_coboundary_coordinates]
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerLineCochain ρ z.val u) =
      (modelHomOf ρ psiEdge psiEdge_smul u, (modelHomOf ρ psiLine psiLine_smul z.val, 0)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc]
  have hdz : (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ modelHomOf ρ psiLine psiLine_smul z.val = 0 :=
    modelHomOf_cocycle ρ psiLine psiLine_smul z
  have h1 := flagLine_comp_modelHomOf ρ z.val u hu
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -((prodComplex Γ6 RationalGL3 Flag).d 2 1 ≫ modelHomOf ρ psiEdge psiEdge_smul u) +
      flagLineHom.hom.f 2 ≫ modelHomOf ρ psiLine psiLine_smul z.val -
      flagPlaneHom.hom.f 2 ≫ (0 : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ coeffRep ρ) = 0
    rw [h1, comp_zero]
    abel
  · exact hdz
  · exact comp_zero

theorem innerPlaneCochain_cocycle (z : cocycles N6 (functionRepresentation ρ (Flags .plane)))
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.val.1 x (endpoint .plane e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    coneR.d 3 2 ≫ innerPlaneCochain ρ z.val u = 0 := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 2).injective
  rw [cone_coboundary_coordinates]
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerPlaneCochain ρ z.val u) =
      (-modelHomOf ρ psiEdge psiEdge_smul u, (0, modelHomOf ρ psiPlane psiPlane_smul z.val)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc]
  have hdz : (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ modelHomOf ρ psiPlane psiPlane_smul z.val = 0 :=
    modelHomOf_cocycle ρ psiPlane psiPlane_smul z
  have h1 := flagPlane_comp_modelHomOf ρ z.val u hu
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -((prodComplex Γ6 RationalGL3 Flag).d 2 1 ≫ (-modelHomOf ρ psiEdge psiEdge_smul u)) +
      flagLineHom.hom.f 2 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ coeffRep ρ) -
      flagPlaneHom.hom.f 2 ≫ modelHomOf ρ psiPlane psiPlane_smul z.val = 0
    rw [h1, comp_zero, Preadditive.comp_neg]
    abel
  · exact comp_zero
  · exact hdz

theorem cls2_zero (K : CochainComplex (ModuleCat.{0} ℚ) ℕ) (h : (K.d 2 3).hom (0 : K.X 2) = 0) :
    cls2 K 0 h = 0 :=
  (cls2_eq_zero_iff K 0 h).2 ⟨0, map_zero _⟩

/-- The class in `H²(∂M; ρ)` of the lift `(e, l, 0)` of an inner line class. -/
def innerLineCone (z : cocycles N6 (functionRepresentation ρ (Flags .line)))
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.val.1 x (endpoint .line e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    (homCochains coneR (coeffRep ρ)).homology 2 :=
  cls2 (homCochains coneR (coeffRep ρ)) (innerLineCochain ρ z.val u)
    (innerLineCochain_cocycle ρ z u hu)

/-- The class in `H²(∂M; ρ)` of the lift `(e, 0, p)` of an inner plane class. -/
def innerPlaneCone (z : cocycles N6 (functionRepresentation ρ (Flags .plane)))
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.val.1 x (endpoint .plane e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    (homCochains coneR (coeffRep ρ)).homology 2 :=
  cls2 (homCochains coneR (coeffRep ρ)) (innerPlaneCochain ρ z.val u)
    (innerPlaneCochain_cocycle ρ z u hu)

theorem innerLineCone_line (z : cocycles N6 (functionRepresentation ρ (Flags .line)))
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.val.1 x (endpoint .line e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    (homologyMap (homPullback coneLine (coeffRep ρ)) 2).hom (innerLineCone ρ z u hu) =
      modelCls ρ psiLine psiLine_smul z := by
  unfold innerLineCone modelCls
  refine (cls2_map _ (homPullback coneLine (coeffRep ρ)) _ _
    (map_cocycle _ (homPullback coneLine (coeffRep ρ)) _ (innerLineCochain_cocycle ρ z u hu))).trans ?_
  refine cls2_congr _ _ _ ?_
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
    (innerLineCochain ρ z.val u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerLineCochain ρ z.val u) =
      (modelHomOf ρ psiEdge psiEdge_smul u, (modelHomOf ρ psiLine psiLine_smul z.val, 0)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun t => t.2.1) h).symm

theorem innerLineCone_plane (z : cocycles N6 (functionRepresentation ρ (Flags .line)))
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.val.1 x (endpoint .line e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    (homologyMap (homPullback conePlane (coeffRep ρ)) 2).hom (innerLineCone ρ z u hu) = 0 := by
  unfold innerLineCone
  refine (cls2_map _ (homPullback conePlane (coeffRep ρ)) _ _
    (map_cocycle _ (homPullback conePlane (coeffRep ρ)) _ (innerLineCochain_cocycle ρ z u hu))).trans ?_
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
    (innerLineCochain ρ z.val u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerLineCochain ρ z.val u) =
      (modelHomOf ρ psiEdge psiEdge_smul u, (modelHomOf ρ psiLine psiLine_smul z.val, 0)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  have h0 : (homPullback conePlane (coeffRep ρ)).f 2 (innerLineCochain ρ z.val u) = 0 :=
    (congrArg (fun t => t.2.2) h).symm
  exact (cls2_congr _ _ (map_zero _) h0).trans (cls2_zero _ (map_zero _))

theorem innerPlaneCone_plane (z : cocycles N6 (functionRepresentation ρ (Flags .plane)))
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.val.1 x (endpoint .plane e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    (homologyMap (homPullback conePlane (coeffRep ρ)) 2).hom (innerPlaneCone ρ z u hu) =
      modelCls ρ psiPlane psiPlane_smul z := by
  unfold innerPlaneCone modelCls
  refine (cls2_map _ (homPullback conePlane (coeffRep ρ)) _ _
    (map_cocycle _ (homPullback conePlane (coeffRep ρ)) _ (innerPlaneCochain_cocycle ρ z u hu))).trans ?_
  refine cls2_congr _ _ _ ?_
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
    (innerPlaneCochain ρ z.val u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerPlaneCochain ρ z.val u) =
      (-modelHomOf ρ psiEdge psiEdge_smul u, (0, modelHomOf ρ psiPlane psiPlane_smul z.val)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun t => t.2.2) h).symm

theorem innerPlaneCone_line (z : cocycles N6 (functionRepresentation ρ (Flags .plane)))
    (u : cochains N6 (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, z.val.1 x (endpoint .plane e) =
      (differentialOne N6 (functionRepresentation ρ Edges) u).1 x e) :
    (homologyMap (homPullback coneLine (coeffRep ρ)) 2).hom (innerPlaneCone ρ z u hu) = 0 := by
  unfold innerPlaneCone
  refine (cls2_map _ (homPullback coneLine (coeffRep ρ)) _ _
    (map_cocycle _ (homPullback coneLine (coeffRep ρ)) _ (innerPlaneCochain_cocycle ρ z u hu))).trans ?_
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
    (innerPlaneCochain ρ z.val u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerPlaneCochain ρ z.val u) =
      (-modelHomOf ρ psiEdge psiEdge_smul u, (0, modelHomOf ρ psiPlane psiPlane_smul z.val)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  have h0 : (homPullback coneLine (coeffRep ρ)).f 2 (innerPlaneCochain ρ z.val u) = 0 :=
    (congrArg (fun t => t.2.1) h).symm
  exact (cls2_congr _ _ (map_zero _) h0).trans (cls2_zero _ (map_zero _))

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
