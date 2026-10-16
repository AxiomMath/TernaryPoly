module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Basic

@[expose] public section


/-!
# Dictionary, line side: the Rep-level cone pairing of the lifts is the function-level boundary cup product

For a spanning coinvariant cycle `v` of the model cone `coneR`, a line cocycle `z` with edge primitive `w`, a plane
cocycle `y` and a vertex primitive `γ` of `z ⌣ y^φ`, the pairing `ev ∘ (B ⊗ A) ∘ Δ_{2,2}(v)` of the cone cochains
`B = lineLiftB z w`, `A = lineLiftA T r y s` (the Rep-level incarnations of `(z, 0, w)` and `(y^φ, 0, s^φ)`) equals
`r (evalOmega (cornerChain v) (boundaryValue T w y γ))`: it is read off on the corner chain of `v` from the coordinate
description `PushCone.pair_cycle`, the plane term being zero because `B` has no plane component, and the primitive of
the line pairing being the Rep-level `vertexHom`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

variable {n : ℕ} {χ : RankOneCharacter}

theorem modelHomOf_single {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
    (ρ : Representation ℂ RationalGL3 V) {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z] (ψ : X ≃ Z)
    (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x) {k : ℕ}
    (f : cochains N6 (functionRepresentation ρ X) k) (y : (Fin (k + 1) → RationalGL3) × Z) :
    (modelHomOf ρ ψ hψ f).hom (MonoidAlgebra.single y 1) = f.1 y.1 (ψ.symm y.2) :=
  congrFun (homFunA_modelHomOf ρ ψ hψ f) y

theorem flagLine_f_single (k : ℕ) (x : Fin (k + 1) → RationalGL3) (ε : TernaryPoly.SymmetricSpaceBoundaryMV.Flag) :
    (flagLineHom.hom.f k).hom (MonoidAlgebra.single (x, ε) 1) =
      MonoidAlgebra.single (x, TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine ε) 1 :=
  prodMapHom_f_single Γ6 RationalGL3 _ _ _ k x ε

theorem flagPlane_f_single (k : ℕ) (x : Fin (k + 1) → RationalGL3) (ε : TernaryPoly.SymmetricSpaceBoundaryMV.Flag) :
    (flagPlaneHom.hom.f k).hom (MonoidAlgebra.single (x, ε) 1) =
      MonoidAlgebra.single (x, TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane ε) 1 :=
  prodMapHom_f_single Γ6 RationalGL3 _ _ _ k x ε

theorem psiLine_flagLine (ε : TernaryPoly.SymmetricSpaceBoundaryMV.Flag) :
    psiLine.symm (TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine ε) =
      endpoint .line (psiEdge.symm ε) := by
  rw [Equiv.symm_apply_eq]
  have := psiEdge_line (psiEdge.symm ε)
  rw [Equiv.apply_symm_apply] at this
  exact this

theorem psiPlane_flagPlane (ε : TernaryPoly.SymmetricSpaceBoundaryMV.Flag) :
    psiPlane.symm (TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane ε) =
      endpoint .plane (psiEdge.symm ε) := by
  rw [Equiv.symm_apply_eq]
  have := psiEdge_plane (psiEdge.symm ε)
  rw [Equiv.apply_symm_apply] at this
  exact this

theorem lineA_single {W : Rep.{0} ℚ Γ6} (k : ℕ) (u : Fin (k + 1) → RationalGL3)
    (ε : TernaryPoly.SymmetricSpaceBoundaryMV.Flag) (g : (prodComplex Γ6 RationalGL3 Line).X k ⟶ W) :
    (flagLineHom.hom.f k ≫ g).hom (MonoidAlgebra.single (u, ε) 1) =
      g.hom (MonoidAlgebra.single (u, TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine ε) 1) := by
  change g.hom ((flagLineHom.hom.f k).hom _) = _
  exact congrArg g.hom (flagLine_f_single k u ε)

theorem planeA_single {W : Rep.{0} ℚ Γ6} (k : ℕ) (u : Fin (k + 1) → RationalGL3)
    (ε : TernaryPoly.SymmetricSpaceBoundaryMV.Flag) (g : (prodComplex Γ6 RationalGL3 Plane).X k ⟶ W) :
    (flagPlaneHom.hom.f k ≫ g).hom (MonoidAlgebra.single (u, ε) 1) =
      g.hom (MonoidAlgebra.single (u, TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane ε) 1) := by
  change g.hom ((flagPlaneHom.hom.f k).hom _) = _
  exact congrArg g.hom (flagPlane_f_single k u ε)

/-- Evaluation of a morphism `ℚ[V^4 × Flag] ⟶ 𝟙_` on the corner projection of a chain `v` of the cone. -/
theorem hom_eq_evalOmega_r (F : resFlag.complex.X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (r : ℂ →ₗ[ℚ] ℚ)
    (f : (Fin 4 → RationalGL3) → Edges → ℂ)
    (h : ∀ (x : Fin 4 → RationalGL3) (ε : Flag), F.hom (MonoidAlgebra.single (x, ε) 1) = r (f x (psiEdge.symm ε)))
    (v : coneR.X 4) : F.hom ((modelPush.pA 3).hom v) = r (evalOmega (cornerChain v) f) := by
  have h1 : (modelPush.pA 3).hom v = cornerChain v := congrArg (fun m => m.hom v) pA_eq_fstX
  rw [h1]
  exact hom_eq_evalChain_r (Y := (Fin (3 + 1) → RationalGL3) × Flag) F r (fun y => f y.1 (psiEdge.symm y.2))
    (fun y => h y.1 y.2) (cornerChain v)

section Line

variable (T : DualityData n χ) (r : ℂ →ₗ[ℚ] ℚ)

theorem lineLiftB_corner (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) :
    modelPush.iA 1 ≫ lineLiftB z w = modelHomOf (rationalCoefficientComponent n χ) psiEdge psiEdge_smul
      (restrictN6 (functionRepresentation (rationalCoefficientComponent n χ) Edges) w) :=
  innerLine_corner _ _ _

theorem lineLiftB_line (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) :
    modelPush.iL 2 ≫ lineLiftB z w = modelHomOf (rationalCoefficientComponent n χ) psiLine psiLine_smul
      (restrictN6 (flagRepresentation (rationalCoefficientComponent n χ) .line) z.val) :=
  innerLine_line _ _ _

theorem lineLiftB_plane (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) :
    modelPush.iP 2 ≫ lineLiftB z w = 0 :=
  innerLine_plane _ _ _

theorem lineLiftA_corner (y : MaximalCycles n χ .plane) (s : EdgeCochains n χ 1) :
    modelPush.iA 1 ≫ lineLiftA T r y s =
      modelHomOf (twistRep T) psiEdge psiEdge_smul (twistCochain1 T s) ≫ pairHom T r := by
  unfold lineLiftA
  rw [← Category.assoc, innerLine_corner]

theorem lineLiftA_line (y : MaximalCycles n χ .plane) (s : EdgeCochains n χ 1) :
    modelPush.iL 2 ≫ lineLiftA T r y s =
      modelHomOf (twistRep T) psiLine psiLine_smul (twistCochain2 T y.val) ≫ pairHom T r := by
  unfold lineLiftA
  rw [← Category.assoc, innerLine_line]

theorem lineLiftA_plane (y : MaximalCycles n χ .plane) (s : EdgeCochains n χ 1) :
    modelPush.iP 2 ≫ lineLiftA T r y s = 0 := by
  unfold lineLiftA
  rw [← Category.assoc, innerLine_plane, zero_comp]

/-- Values of the lifts on basis simplices. -/
theorem lineLiftB_corner_val (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (y : (Fin 2 → RationalGL3) × Flag) :
    (modelPush.iA 1 ≫ lineLiftB z w).hom (MonoidAlgebra.single y 1) = w.val y.1 (psiEdge.symm y.2) :=
  (congrArg (fun m => m.hom (MonoidAlgebra.single y 1)) (lineLiftB_corner z w)).trans
    (modelHomOf_single _ _ _ _ y)

theorem lineLiftB_line_val (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (y : (Fin 3 → RationalGL3) × Line) :
    (modelPush.iL 2 ≫ lineLiftB z w).hom (MonoidAlgebra.single y 1) = z.val.val y.1 (psiLine.symm y.2) :=
  (congrArg (fun m => m.hom (MonoidAlgebra.single y 1)) (lineLiftB_line z w)).trans
    (modelHomOf_single _ _ _ _ y)

theorem lineLiftA_line_val (y : MaximalCycles n χ .plane) (s : EdgeCochains n χ 1)
    (u : (Fin 3 → RationalGL3) × Line) :
    (modelPush.iL 2 ≫ lineLiftA T r y s).hom (MonoidAlgebra.single u 1) =
      (pairHom T r).hom (y.val.val (fun i => T.φ (u.1 i)) (T.dualFlag (psiLine.symm u.2))) :=
  (congrArg (fun m => m.hom (MonoidAlgebra.single u 1)) (lineLiftA_line T r y s)).trans
    (congrArg (pairHom T r).hom (modelHomOf_single _ _ _ _ u))

theorem lineLiftA_flag_val (y : MaximalCycles n χ .plane) (s : EdgeCochains n χ 1)
    (u : Fin 3 → RationalGL3) (ε : Flag) :
    (flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ lineLiftA T r y s).hom (MonoidAlgebra.single (u, ε) 1) =
      (pairHom T r).hom (y.val.val (fun i => T.φ (u i)) (T.dualFlag (endpoint .line (psiEdge.symm ε)))) := by
  refine (lineA_single 2 u ε _).trans ?_
  refine (lineLiftA_line_val T r y s _).trans ?_
  rw [psiLine_flagLine]

/-- Rep-level vertex primitive on the line resolution: its coboundary is the line pairing of the lifts. -/
theorem line_vertex_d (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (s : EdgeCochains n χ 1) (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
    (hγ1 : γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3)
    (hγ2 : ∀ x F, differentialThreeRaw γ x F =
      T.B (z.val.val ![x 0, x 1, x 2] F) (y.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)] (T.dualFlag F))) :
    (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ vertexHom psiLine psiLine_smul r γ hγ1 =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫
        ((modelPush.iL 2 ≫ lineLiftB z w) ⊗ₘ (modelPush.iL 2 ≫ lineLiftA T r y s)) ≫
          evalRep (coeffRep (rationalCoefficientComponent n χ)) := by
  refine hom_ext_single ((Fin (4 + 1) → RationalGL3) × Line) _ (fun ⟨x, F⟩ => ?_)
  refine (vertexHom_d_single psiLine psiLine_smul r γ hγ1 x F).trans ?_
  refine Eq.trans ?_ (delta_pair_single (evalRep (coeffRep (rationalCoefficientComponent n χ))) 2 2 4 rfl
    (modelPush.iL 2 ≫ lineLiftB z w) (modelPush.iL 2 ≫ lineLiftA T r y s) (x, F)).symm
  rw [lineLiftB_line_val, lineLiftA_line_val]
  refine Eq.trans ?_ ((evalRep_tmul _ _ _).trans (pairHom_apply T r _ _)).symm
  refine congrArg r ?_
  rw [hγ2]
  simp only [frontFace, backFace]
  rw [front_3, back_3, vec3_phi]

/-- **Dictionary, line side.** -/
theorem pair_lineLift (v : coneR.X 4) (hv : IsCoinvCycle v)
    (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (s : EdgeCochains n χ 1) (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ) (hγ : VertexPrimitive T z y γ) :
    (evalRep (coeffRep (rationalCoefficientComponent n χ))).hom
      ((lineLiftB z w ⊗ₘ lineLiftA T r y s).hom ((modelDiagSystem.Δ 2 2 4 rfl).hom v)) =
    r (evalOmega (cornerChain v) (boundaryValue T w y γ)) := by
  obtain ⟨hγ1, hγ2⟩ := hγ
  have hL := line_vertex_d T r z w y s γ hγ1 hγ2
  have hP : (resPlane.complex).d 4 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫
        ((modelPush.iP 2 ≫ lineLiftB z w) ⊗ₘ (modelPush.iP 2 ≫ lineLiftA T r y s)) ≫
          evalRep (coeffRep (rationalCoefficientComponent n χ)) := by
    rw [lineLiftB_plane, lineLiftA_plane]
    simp
  have key := modelPush.pair_cycle (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) (lineLiftB z w) (lineLiftA T r y s)
    (evalRep (coeffRep (rationalCoefficientComponent n χ))) v hv
    (vertexHom psiLine psiLine_smul r γ hγ1) 0 hL hP
  refine Eq.trans key ?_
  refine hom_eq_evalOmega_r _ r (boundaryValue T w y γ) ?_ v
  intro x ε
  have e1 : ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫
      ((modelPush.iA 1 ≫ lineLiftB z w) ⊗ₘ (flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ lineLiftA T r y s)) ≫
        evalRep (coeffRep (rationalCoefficientComponent n χ))).hom (MonoidAlgebra.single (x, ε) 1) =
      r (T.B (w.val ![x 0, x 1] (psiEdge.symm ε))
        (y.val.val ![T.φ (x 1), T.φ (x 2), T.φ (x 3)] (T.dualFlag (endpoint .line (psiEdge.symm ε))))) := by
    refine (delta_pair_single (evalRep (coeffRep (rationalCoefficientComponent n χ))) 1 2 3 rfl
      (modelPush.iA 1 ≫ lineLiftB z w) (flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ lineLiftA T r y s) (x, ε)).trans ?_
    rw [lineLiftB_corner_val]
    simp only [frontFace, backFace]
    rw [lineLiftA_flag_val]
    refine ((evalRep_tmul _ _ _).trans (pairHom_apply T r _ _)).trans ?_
    rw [front_1, back_1, vec3_phi]
  have e2 : ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫
      ((flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ lineLiftB z w) ⊗ₘ (modelPush.iA 1 ≫ lineLiftA T r y s)) ≫
        evalRep (coeffRep (rationalCoefficientComponent n χ))).hom (MonoidAlgebra.single (x, ε) 1) = 0 := by
    rw [lineLiftB_plane, comp_zero, PushCone.zero_tensorHom', zero_comp, comp_zero]
    rfl
  have e3 : (flagLineHom.hom.f 3 ≫ vertexHom psiLine psiLine_smul r γ hγ1).hom
      (MonoidAlgebra.single (x, ε) 1) = r (γ x (endpoint .line (psiEdge.symm ε))) := by
    refine (lineA_single 3 x ε _).trans ?_
    rw [vertexHom_single, psiLine_flagLine]
  have e4 : (flagPlaneHom.hom.f 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))).hom
      (MonoidAlgebra.single (x, ε) 1) = 0 := by
    rw [comp_zero]
    rfl
  refine (hom4_apply _ _ _ _ _).trans ?_
  rw [e1, e2, e3, e4]
  simp [boundaryValue]

end Line

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
