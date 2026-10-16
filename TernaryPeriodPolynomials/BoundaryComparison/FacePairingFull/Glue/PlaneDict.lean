module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.CornerCycle

@[expose] public section


/-!
# Dictionary, plane side (the plane-supported twin)

The plane-supported cone cochains `B = planeLiftB z w` (coordinates `(-w, 0, z)`, `z` a plane cocycle with edge primitive `w`)
and `A = planeLiftA T r y s` (coordinates `(-s^φ, 0, y^φ)`, `y` a line cocycle with edge primitive `s`) pair on a coinvariant
cycle `v` of the model cone to `- r (evalOmega (cornerChain v) (boundaryValueP T w y γ))`.  The cone `coneR` has the line
in the first slot, so a plane-supported cochain contributes through the second corner term `r_P z ⌣ (corner of A)` of the
Alexander-Whitney diagonal of the cone, `-(z|_F ⌣ s^φ) + γ`; this differs from the function-level corner cochain
`w ⌣ y^φ|_F - γ` of `boundaryValueP` (the plane-first cone cup product) by `-(z|_F ⌣ s^φ - w ⌣ ds^φ) = -d(w ⌣ s^φ)`
(Leibniz, `edgeDualCupP`), whose evaluation on the corner chain of a cycle vanishes (`evalOmega_differentialTwo`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

variable {n : ℕ} {χ : RankOneCharacter}

section Coordinates

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

theorem innerPlane_corner (z : cochains N6 (functionRepresentation ρ (Flags .plane)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    modelPush.iA 1 ≫ innerPlaneCochain ρ z u = -modelHomOf ρ psiEdge psiEdge_smul u := by
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerPlaneCochain ρ z u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerPlaneCochain ρ z u) =
      (-modelHomOf ρ psiEdge psiEdge_smul u, (0, modelHomOf ρ psiPlane psiPlane_smul z)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg Prod.fst h).symm

theorem innerPlane_line (z : cochains N6 (functionRepresentation ρ (Flags .plane)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    modelPush.iL 2 ≫ innerPlaneCochain ρ z u = 0 := by
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerPlaneCochain ρ z u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerPlaneCochain ρ z u) =
      (-modelHomOf ρ psiEdge psiEdge_smul u, (0, modelHomOf ρ psiPlane psiPlane_smul z)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun p => p.2.1) h).symm

theorem innerPlane_plane (z : cochains N6 (functionRepresentation ρ (Flags .plane)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    modelPush.iP 2 ≫ innerPlaneCochain ρ z u = modelHomOf ρ psiPlane psiPlane_smul z := by
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerPlaneCochain ρ z u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerPlaneCochain ρ z u) =
      (-modelHomOf ρ psiEdge psiEdge_smul u, (0, modelHomOf ρ psiPlane psiPlane_smul z)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun p => p.2.2) h).symm

end Coordinates

section Plane

variable (T : DualityDataP n χ) (r : ℂ →ₗ[ℚ] ℚ)

theorem planeLiftB_line (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1) :
    modelPush.iL 2 ≫ planeLiftB z w = 0 :=
  innerPlane_line _ _ _

theorem planeLiftB_plane (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1) :
    modelPush.iP 2 ≫ planeLiftB z w = modelHomOf (rationalCoefficientComponent n χ) psiPlane psiPlane_smul
      (restrictN6 (flagRepresentation (rationalCoefficientComponent n χ) .plane) z.val) :=
  innerPlane_plane _ _ _

theorem planeLiftA_corner (y : MaximalCycles n χ .line) (s : EdgeCochains n χ 1) :
    modelPush.iA 1 ≫ planeLiftA T r y s =
      -(modelHomOf (twistRepP T) psiEdge psiEdge_smul (twistCochain1P T s) ≫ pairHomP T r) := by
  unfold planeLiftA
  rw [← Category.assoc, innerPlane_corner, Preadditive.neg_comp]

theorem planeLiftA_line (y : MaximalCycles n χ .line) (s : EdgeCochains n χ 1) :
    modelPush.iL 2 ≫ planeLiftA T r y s = 0 := by
  unfold planeLiftA
  rw [← Category.assoc, innerPlane_line, zero_comp]

theorem planeLiftA_plane (y : MaximalCycles n χ .line) (s : EdgeCochains n χ 1) :
    modelPush.iP 2 ≫ planeLiftA T r y s =
      modelHomOf (twistRepP T) psiPlane psiPlane_smul (twistCochain2P T y.val) ≫ pairHomP T r := by
  unfold planeLiftA
  rw [← Category.assoc, innerPlane_plane]

/-- Values of the lifts on basis simplices. -/
theorem planeLiftB_plane_val (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1)
    (y : (Fin 3 → RationalGL3) × Plane) :
    (modelPush.iP 2 ≫ planeLiftB z w).hom (MonoidAlgebra.single y 1) = z.val.val y.1 (psiPlane.symm y.2) :=
  (congrArg (fun m => m.hom (MonoidAlgebra.single y 1)) (planeLiftB_plane z w)).trans
    (modelHomOf_single _ _ _ _ y)

theorem planeLiftA_plane_val (y : MaximalCycles n χ .line) (s : EdgeCochains n χ 1)
    (u : (Fin 3 → RationalGL3) × Plane) :
    (modelPush.iP 2 ≫ planeLiftA T r y s).hom (MonoidAlgebra.single u 1) =
      (pairHomP T r).hom (y.val.val (fun i => T.φ (u.1 i)) (T.dualFlag (psiPlane.symm u.2))) :=
  (congrArg (fun m => m.hom (MonoidAlgebra.single u 1)) (planeLiftA_plane T r y s)).trans
    (congrArg (pairHomP T r).hom (modelHomOf_single _ _ _ _ u))

theorem planeLiftB_flag_val (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1)
    (u : Fin 3 → RationalGL3) (ε : Flag) :
    (flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ planeLiftB z w).hom (MonoidAlgebra.single (u, ε) 1) =
      z.val.val u (endpoint .plane (psiEdge.symm ε)) := by
  refine (planeA_single 2 u ε _).trans ?_
  refine (planeLiftB_plane_val z w _).trans ?_
  rw [psiPlane_flagPlane]

theorem planeLiftA_corner_val (y : MaximalCycles n χ .line) (s : EdgeCochains n χ 1)
    (u : (Fin 2 → RationalGL3) × Flag) :
    (modelPush.iA 1 ≫ planeLiftA T r y s).hom (MonoidAlgebra.single u 1) =
      -((pairHomP T r).hom (s.val (fun i => T.φ (u.1 i)) (T.dualEdge (psiEdge.symm u.2)))) :=
  (congrArg (fun m => m.hom (MonoidAlgebra.single u 1)) (planeLiftA_corner T r y s)).trans
    (congrArg (fun t => -t) (congrArg (pairHomP T r).hom (modelHomOf_single _ _ _ _ u)))

/-- Rep-level vertex primitive on the plane resolution: its coboundary is the plane pairing of the lifts. -/
theorem plane_vertex_d (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .line)
    (s : EdgeCochains n χ 1) (γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
    (hγ1 : γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3)
    (hγ2 : ∀ x F, differentialThreeRaw γ x F =
      T.B (z.val.val ![x 0, x 1, x 2] F) (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))) :
    (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ vertexHom psiPlane psiPlane_smul r γ hγ1 =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫
        ((modelPush.iP 2 ≫ planeLiftB z w) ⊗ₘ (modelPush.iP 2 ≫ planeLiftA T r y s)) ≫
          evalRep (coeffRep (rationalCoefficientComponent n χ)) := by
  refine hom_ext_single ((Fin (4 + 1) → RationalGL3) × Plane) _ (fun ⟨x, F⟩ => ?_)
  refine (vertexHom_d_single psiPlane psiPlane_smul r γ hγ1 x F).trans ?_
  refine Eq.trans ?_ (delta_pair_single (evalRep (coeffRep (rationalCoefficientComponent n χ))) 2 2 4 rfl
    (modelPush.iP 2 ≫ planeLiftB z w) (modelPush.iP 2 ≫ planeLiftA T r y s) (x, F)).symm
  rw [planeLiftB_plane_val, planeLiftA_plane_val]
  refine Eq.trans ?_ ((evalRep_tmul _ _ _).trans (pairHomP_apply T r _ _)).symm
  refine congrArg r ?_
  rw [hγ2]
  simp only [frontFace, backFace]
  rw [front_3, back_3, vec3_phiP]

/-- **Dictionary, plane side.** -/
theorem pair_planeLift (v : coneR.X 4) (hv : IsCoinvCycle v)
    (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1) (hw : EdgePrimitiveP z w)
    (y : MaximalCycles n χ .line) (s : EdgeCochains n χ 1)
    (hs : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e)
    (γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ) (hγ : VertexPrimitiveP T z y γ) :
    (evalRep (coeffRep (rationalCoefficientComponent n χ))).hom
      ((planeLiftB z w ⊗ₘ planeLiftA T r y s).hom ((modelDiagSystem.Δ 2 2 4 rfl).hom v)) =
    -r (evalOmega (cornerChain v) (boundaryValueP T w y γ)) := by
  obtain ⟨hγ1, hγ2⟩ := hγ
  have hL : (resLine.complex).d 4 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫
        ((modelPush.iL 2 ≫ planeLiftB z w) ⊗ₘ (modelPush.iL 2 ≫ planeLiftA T r y s)) ≫
          evalRep (coeffRep (rationalCoefficientComponent n χ)) := by
    rw [planeLiftB_line, planeLiftA_line]
    simp
  have hP := plane_vertex_d T r z w y s γ hγ1 hγ2
  have key := modelPush.pair_cycle (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) (planeLiftB z w) (planeLiftA T r y s)
    (evalRep (coeffRep (rationalCoefficientComponent n χ))) v hv 0
    (vertexHom psiPlane psiPlane_smul r γ hγ1) hL hP
  refine Eq.trans key ?_
  -- the corner function of the Rep-level expression
  let Cg : (Fin 4 → RationalGL3) → Edges → ℂ := fun x e =>
    T.B (z.val.val ![x 0, x 1, x 2] (endpoint .plane e)) (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge e)) -
      γ x (endpoint .plane e)
  have hid : (fun x e => -Cg x e) = -(boundaryValueP T w y γ) -
      differentialTwo N6 (functionRepresentation scalarTrivial Edges)
        (restrictN6 (functionRepresentation scalarTrivial Edges) (edgeDualCupP T w s)) := by
    funext x e
    have hY : y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .plane e)) =
        s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge e) - s.val ![T.φ (x 1), T.φ (x 3)] (T.dualEdge e) +
          s.val ![T.φ (x 1), T.φ (x 2)] (T.dualEdge e) := by
      rw [← T.endpoint_dualEdge e]
      exact hs ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualEdge e)
    have h₁ : z.val.val ![x 0, x 1, x 2] (endpoint .plane e) =
        w.val ![x 1, x 2] e - w.val ![x 0, x 2] e + w.val ![x 0, x 1] e :=
      hw ![x 0, x 1, x 2] e
    change -(T.B (z.val.val ![x 0, x 1, x 2] (endpoint .plane e)) (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge e)) -
        γ x (endpoint .plane e)) =
      -(T.B (w.val ![x 0, x 1] e) (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)]
          (T.dualFlag (endpoint .plane e))) - γ x (endpoint .plane e)) -
        (T.B (w.val ![x 1, x 2] e) (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge e)) -
          T.B (w.val ![x 0, x 2] e) (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge e)) +
          T.B (w.val ![x 0, x 1] e) (s.val ![T.φ (x 1), T.φ (x 3)] (T.dualEdge e)) -
          T.B (w.val ![x 0, x 1] e) (s.val ![T.φ (x 1), T.φ (x 2)] (T.dualEdge e)))
    rw [hY, h₁]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    abel
  have hmain := hom_eq_evalOmega_r
    (((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫
          ((modelPush.iA 1 ≫ planeLiftB z w) ⊗ₘ (flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ planeLiftA T r y s)) ≫
            evalRep (coeffRep (rationalCoefficientComponent n χ)) +
        (nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫
          ((flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ planeLiftB z w) ⊗ₘ (modelPush.iA 1 ≫ planeLiftA T r y s)) ≫
            evalRep (coeffRep (rationalCoefficientComponent n χ))) -
        flagLineHom.hom.f 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) +
        flagPlaneHom.hom.f 3 ≫ vertexHom psiPlane psiPlane_smul r γ hγ1) r (fun x e => -Cg x e) ?_ v
  · rw [hmain, hid, map_sub, map_neg, map_sub, evalOmega_differentialTwo v hv r, sub_zero, map_neg]
  intro x ε
  have e1 : ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫
      ((modelPush.iA 1 ≫ planeLiftB z w) ⊗ₘ (flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ planeLiftA T r y s)) ≫
        evalRep (coeffRep (rationalCoefficientComponent n χ))).hom (MonoidAlgebra.single (x, ε) 1) = 0 := by
    rw [planeLiftA_line, comp_zero, PushCone.tensorHom_zero', zero_comp, comp_zero]
    rfl
  have e2 : ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫
      ((flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ planeLiftB z w) ⊗ₘ (modelPush.iA 1 ≫ planeLiftA T r y s)) ≫
        evalRep (coeffRep (rationalCoefficientComponent n χ))).hom (MonoidAlgebra.single (x, ε) 1) =
      -r (T.B (z.val.val ![x 0, x 1, x 2] (endpoint .plane (psiEdge.symm ε)))
          (s.val ![T.φ (x 2), T.φ (x 3)] (T.dualEdge (psiEdge.symm ε)))) := by
    refine (delta_pair_single (evalRep (coeffRep (rationalCoefficientComponent n χ))) 2 1 3 rfl
      (flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ planeLiftB z w) (modelPush.iA 1 ≫ planeLiftA T r y s) (x, ε)).trans ?_
    rw [planeLiftB_flag_val, planeLiftA_corner_val]
    simp only [frontFace, backFace]
    refine (congrArg (evalRep (coeffRep (rationalCoefficientComponent n χ))).hom
      (TensorProduct.tmul_neg _ _)).trans ?_
    refine (map_neg (evalRep (coeffRep (rationalCoefficientComponent n χ))).hom _).trans ?_
    refine (congrArg (fun t => -t) ((evalRep_tmul _ _ _).trans (pairHomP_apply T r _ _))).trans ?_
    rw [front_2, back_2, vec2_phiP]
  have e3 : (flagLineHom.hom.f 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))).hom
      (MonoidAlgebra.single (x, ε) 1) = 0 := by
    rw [comp_zero]
    rfl
  have e4 : (flagPlaneHom.hom.f 3 ≫ vertexHom psiPlane psiPlane_smul r γ hγ1).hom
      (MonoidAlgebra.single (x, ε) 1) = r (γ x (endpoint .plane (psiEdge.symm ε))) := by
    refine (planeA_single 3 x ε _).trans ?_
    rw [vertexHom_single, psiPlane_flagPlane]
  refine (hom4_apply _ _ _ _ _).trans ?_
  rw [e1, e2, e3, e4]
  simp only [Cg, map_neg, map_sub]
  abel

end Plane

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
