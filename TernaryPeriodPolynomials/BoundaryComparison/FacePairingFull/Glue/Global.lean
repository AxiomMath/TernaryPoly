module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Main
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Canon

@[expose] public section


/-!
# Rep-level pairing of the restrictions of two global classes

For global cocycles `c1, c2` of the arithmetic level (coefficients `ρ`), the cone cochains `globalB c1 = coneToPt^* c1`
(corner component zero, constant-on-faces components) and `globalA T r c2 = coneToPt^* (c2 ∘ φ)` composed with `pairHom T r`
(values in the contragredient) pair on a coinvariant cycle `v` of the model cone to the evaluation, on the corner chain of
`v`, of the difference of vertex primitives `γP ∘ endpoint - γL ∘ endpoint` of the face cups
`c1 ⌣ (c2 ∘ φ)` (`pair_global`): the corner terms of the pairing vanish because both cochains have zero corner component.

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
open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPoly.SingularLocalDuality (dualRepresentation)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

theorem coneToPt_corner {W : Rep.{0} ℚ Γ6} (c : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ W) :
    modelPush.iA 1 ≫ coneToPt.f 2 ≫ c = 0 := by
  rw [← Category.assoc]
  exact (congrArg (fun m => m ≫ c) (signedCornerInclusion_coneDesc flagLineHom.hom flagPlaneHom.hom
    (ptMap Line) (ptMap Plane) line_plane_ptMap 1)).trans (zero_comp)

theorem coneToPt_line : modelPush.iL 2 ≫ coneToPt.f 2 = (ptMap Line).f 2 :=
  signedLineInclusion_coneDesc flagLineHom.hom flagPlaneHom.hom (ptMap Line) (ptMap Plane) line_plane_ptMap 2

theorem coneToPt_plane : modelPush.iP 2 ≫ coneToPt.f 2 = (ptMap Plane).f 2 :=
  signedPlaneInclusion_coneDesc flagLineHom.hom flagPlaneHom.hom (ptMap Line) (ptMap Plane) line_plane_ptMap 2

section Twist

variable {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- The `φ`-twist of a global degree-two cochain of the arithmetic level, as an `N6`-cochain with coefficients `ρ ∘ φ`. -/
def twistGlobal (y : cochains rationalLevel (rationalCoefficientComponent n χ) 2) :
    cochains N6 (twistRep T) 2 :=
  ⟨fun x => y.1 (fun i => T.φ (x i)), by
    intro g x
    have hg : T.φ g.val ∈ rationalLevel := T.level g.val (N6_le_rationalLevel g.property)
    have h1 := y.2 ⟨T.φ g.val, hg⟩ (fun i => T.φ (x i))
    change y.1 (fun i => T.φ (g.val * x i)) = twistRep T g.val (y.1 (fun i => T.φ (x i)))
    simp only [map_mul]
    exact h1⟩

theorem twistGlobal_apply (y : cochains rationalLevel (rationalCoefficientComponent n χ) 2)
    (x : Fin 3 → RationalGL3) : (twistGlobal T y).1 x = y.1 (fun i => T.φ (x i)) := rfl

theorem twistGlobal_cocycle (y : cochains rationalLevel (rationalCoefficientComponent n χ) 2)
    (hy : differentialTwo rationalLevel (rationalCoefficientComponent n χ) y = 0) :
    differentialTwo N6 (twistRep T) (twistGlobal T y) = 0 := by
  funext x
  have h := congrFun hy (fun i => T.φ (x i))
  change y.1 (fun i => T.φ ((![x 1, x 2, x 3] : Fin 3 → RationalGL3) i)) -
      y.1 (fun i => T.φ ((![x 0, x 2, x 3] : Fin 3 → RationalGL3) i)) +
      y.1 (fun i => T.φ ((![x 0, x 1, x 3] : Fin 3 → RationalGL3) i)) -
      y.1 (fun i => T.φ ((![x 0, x 1, x 2] : Fin 3 → RationalGL3) i)) = 0
  simp only [vec3_phi]
  exact h

end Twist

section PairGlobal

variable {n : ℕ} {χ : RankOneCharacter}

/-- The cone cochain `coneToPt^* ptHom` of a global cocycle: zero on the corner, constant on the faces. -/
def globalB (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    coneR.X 2 ⟶ coeffRep (rationalCoefficientComponent n χ) :=
  coneToPt.f 2 ≫ ptHom (rationalCoefficientComponent n χ)
    (restrictN6 (rationalCoefficientComponent n χ) c.val)

/-- The `φ`-twist of a global cocycle as a cone cochain with values in the contragredient. -/
def globalA (T : DualityData n χ) (r : ℂ →ₗ[ℚ] ℚ) (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    coneR.X 2 ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n χ)) :=
  coneToPt.f 2 ≫ ptHom (twistRep T) (twistGlobal T c.val) ≫ pairHom T r

theorem globalB_corner (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    modelPush.iA 1 ≫ globalB c = 0 := coneToPt_corner _

theorem globalA_corner (T : DualityData n χ) (r : ℂ →ₗ[ℚ] ℚ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    modelPush.iA 1 ≫ globalA T r c = 0 := coneToPt_corner _

theorem ptMap_f_single {Z : Type} [MulAction Γ6 Z] {W : Rep.{0} ℚ Γ6} (k : ℕ) (g : (prodComplex Γ6 RationalGL3 PUnit).X k ⟶ W)
    (u : Fin (k + 1) → RationalGL3) (z : Z) :
    ((ptMap Z).f k ≫ g).hom (MonoidAlgebra.single (u, z) 1) = g.hom (MonoidAlgebra.single (u, PUnit.unit) 1) :=
  congrArg g.hom (prodMapHom_f_single Γ6 RationalGL3 Z _ _ k u z)

theorem globalB_line_val (c : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (u : Fin 3 → RationalGL3) (F : Line) :
    (modelPush.iL 2 ≫ globalB c).hom (MonoidAlgebra.single (u, F) 1) = c.val.val u := by
  unfold globalB
  rw [← Category.assoc, coneToPt_line]
  refine (ptMap_f_single 2 _ u F).trans ?_
  exact modelHomOf_single _ (Equiv.refl PUnit) _ _ (u, PUnit.unit)

theorem globalB_plane_val (c : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (u : Fin 3 → RationalGL3) (F : Plane) :
    (modelPush.iP 2 ≫ globalB c).hom (MonoidAlgebra.single (u, F) 1) = c.val.val u := by
  unfold globalB
  rw [← Category.assoc, coneToPt_plane]
  refine (ptMap_f_single 2 _ u F).trans ?_
  exact modelHomOf_single _ (Equiv.refl PUnit) _ _ (u, PUnit.unit)

theorem globalA_line_val (T : DualityData n χ) (r : ℂ →ₗ[ℚ] ℚ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) (u : Fin 3 → RationalGL3) (F : Line) :
    (modelPush.iL 2 ≫ globalA T r c).hom (MonoidAlgebra.single (u, F) 1) =
      (pairHom T r).hom (c.val.val (fun i => T.φ (u i))) := by
  unfold globalA
  rw [← Category.assoc, coneToPt_line]
  refine (ptMap_f_single 2 _ u F).trans ?_
  exact congrArg (pairHom T r).hom (modelHomOf_single _ (Equiv.refl PUnit) _ _ (u, PUnit.unit))

theorem globalA_plane_val (T : DualityData n χ) (r : ℂ →ₗ[ℚ] ℚ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) (u : Fin 3 → RationalGL3) (F : Plane) :
    (modelPush.iP 2 ≫ globalA T r c).hom (MonoidAlgebra.single (u, F) 1) =
      (pairHom T r).hom (c.val.val (fun i => T.φ (u i))) := by
  unfold globalA
  rw [← Category.assoc, coneToPt_plane]
  refine (ptMap_f_single 2 _ u F).trans ?_
  exact congrArg (pairHom T r).hom (modelHomOf_single _ (Equiv.refl PUnit) _ _ (u, PUnit.unit))


theorem pair_global (T : DualityData n χ) (r : ℂ →ₗ[ℚ] ℚ) (v : coneR.X 4) (hv : IsCoinvCycle v)
    (c1 c2 : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (γL : (Fin 4 → RationalGL3) → Flags .line → ℂ)
    (hγL1 : γL ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3)
    (hγL2 : ∀ x F, differentialThreeRaw γL x F =
      T.B (c1.val.val ![x 0, x 1, x 2]) (c2.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)]))
    (γP : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
    (hγP1 : γP ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3)
    (hγP2 : ∀ x F, differentialThreeRaw γP x F =
      T.B (c1.val.val ![x 0, x 1, x 2]) (c2.val.val ![T.φ (x 2), T.φ (x 3), T.φ (x 4)])) :
    (evalRep (coeffRep (rationalCoefficientComponent n χ))).hom
      ((globalB c1 ⊗ₘ globalA T r c2).hom ((modelDiagSystem.Δ 2 2 4 rfl).hom v)) =
    r (evalOmega (cornerChain v) (fun x e => γP x (endpoint .plane e) - γL x (endpoint .line e))) := by
  have hL : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ vertexHom psiLine psiLine_smul r γL hγL1 =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫
        ((modelPush.iL 2 ≫ globalB c1) ⊗ₘ (modelPush.iL 2 ≫ globalA T r c2)) ≫
          evalRep (coeffRep (rationalCoefficientComponent n χ)) := by
    refine hom_ext_single ((Fin (4 + 1) → RationalGL3) × Line) _ (fun ⟨x, F⟩ => ?_)
    refine (vertexHom_d_single psiLine psiLine_smul r γL hγL1 x F).trans ?_
    refine Eq.trans ?_ (delta_pair_single (evalRep (coeffRep (rationalCoefficientComponent n χ))) 2 2 4 rfl
      (modelPush.iL 2 ≫ globalB c1) (modelPush.iL 2 ≫ globalA T r c2) (x, F)).symm
    rw [globalB_line_val, globalA_line_val]
    refine Eq.trans ?_ ((evalRep_tmul _ _ _).trans (pairHom_apply T r _ _)).symm
    refine congrArg r ?_
    rw [hγL2]
    simp only [frontFace, backFace]
    rw [front_3, back_3, vec3_phi]
  have hP : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ vertexHom psiPlane psiPlane_smul r γP hγP1 =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫
        ((modelPush.iP 2 ≫ globalB c1) ⊗ₘ (modelPush.iP 2 ≫ globalA T r c2)) ≫
          evalRep (coeffRep (rationalCoefficientComponent n χ)) := by
    refine hom_ext_single ((Fin (4 + 1) → RationalGL3) × Plane) _ (fun ⟨x, F⟩ => ?_)
    refine (vertexHom_d_single psiPlane psiPlane_smul r γP hγP1 x F).trans ?_
    refine Eq.trans ?_ (delta_pair_single (evalRep (coeffRep (rationalCoefficientComponent n χ))) 2 2 4 rfl
      (modelPush.iP 2 ≫ globalB c1) (modelPush.iP 2 ≫ globalA T r c2) (x, F)).symm
    rw [globalB_plane_val, globalA_plane_val]
    refine Eq.trans ?_ ((evalRep_tmul _ _ _).trans (pairHom_apply T r _ _)).symm
    refine congrArg r ?_
    rw [hγP2]
    simp only [frontFace, backFace]
    rw [front_3, back_3, vec3_phi]
  have key := modelPush.pair_cycle (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) (globalB c1) (globalA T r c2)
    (evalRep (coeffRep (rationalCoefficientComponent n χ))) v hv
    (vertexHom psiLine psiLine_smul r γL hγL1) (vertexHom psiPlane psiPlane_smul r γP hγP1) hL hP
  refine Eq.trans key ?_
  refine hom_eq_evalOmega_r _ r _ ?_ v
  intro x ε
  have e1 : ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫
      ((modelPush.iA 1 ≫ globalB c1) ⊗ₘ (flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ globalA T r c2)) ≫
        evalRep (coeffRep (rationalCoefficientComponent n χ))).hom (MonoidAlgebra.single (x, ε) 1) = 0 := by
    rw [globalB_corner, PushCone.zero_tensorHom', zero_comp, comp_zero]
    rfl
  have e2 : ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫
      ((flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ globalB c1) ⊗ₘ (modelPush.iA 1 ≫ globalA T r c2)) ≫
        evalRep (coeffRep (rationalCoefficientComponent n χ))).hom (MonoidAlgebra.single (x, ε) 1) = 0 := by
    rw [globalA_corner, PushCone.tensorHom_zero', zero_comp, comp_zero]
    rfl
  have e3 : (flagLineHom.hom.f 3 ≫ vertexHom psiLine psiLine_smul r γL hγL1).hom
      (MonoidAlgebra.single (x, ε) 1) = r (γL x (endpoint .line (psiEdge.symm ε))) := by
    refine (lineA_single 3 x ε _).trans ?_
    rw [vertexHom_single, psiLine_flagLine]
  have e4 : (flagPlaneHom.hom.f 3 ≫ vertexHom psiPlane psiPlane_smul r γP hγP1).hom
      (MonoidAlgebra.single (x, ε) 1) = r (γP x (endpoint .plane (psiEdge.symm ε))) := by
    refine (planeA_single 3 x ε _).trans ?_
    rw [vertexHom_single, psiPlane_flagPlane]
  refine (hom4_apply _ _ _ _ _).trans ?_
  rw [e1, e2, e3, e4, map_sub]
  abel

end PairGlobal

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
