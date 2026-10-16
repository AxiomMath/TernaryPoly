module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.BarClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.DiagCup12
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Local

@[expose] public section


/-!
# The corner 3-cocycle of two plane data at a flag, and its class in the group cohomology of the flag stabilizer

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

The plane analogue of `FlagLocal`: `planeFlagCochain π z w' γ = Δ((z|flags) ⊗ (-w')) ≫ π + γ|flags` (the flag 3-cochain of `PlaneDatum.conePair_exists_corner`) is a cocycle
(`planeFlagCochain_d`) and its Shapiro coordinate at a flag is the class of `x ↦ z̄(x₁, x₂) ⌣ (-w̄')(x₃) + γ̄(x₁, x₂, x₃)` (`planeFlag_faceCoord`).
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))

/-- The flag 3-cochain `(z|flags) ⌣ (-w') + γ|flags` of the corner evaluation of two plane data. -/
def planeFlagCochain (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) (w' : (prodComplex Γ6 RationalGL3 Flag).X 1 ⟶ W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) :
    (prodComplex Γ6 RationalGL3 Flag).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6) :=
  ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫ ((flagPlaneHom.hom.f 2 ≫ z) ⊗ₘ (-w')) ≫ π) +
    flagPlaneHom.hom.f 3 ≫ γ

theorem barCochain_flagPlane {k : ℕ} (T : Subgroup Γ6) (F : Flag) {A : Rep.{0} ℚ Γ6}
    (c : (prodComplex Γ6 RationalGL3 Plane).X k ⟶ A) (x : Fin k → T) :
    barCochain T (1 : RationalGL3) F (flagPlaneHom.hom.f k ≫ c) x =
      barCochain T (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F) c x := by
  unfold barCochain
  change c.hom (((flagPlaneHom.hom.f k)).hom (MonoidAlgebra.single _ 1)) = _
  rw [show barSimplex T (1 : RationalGL3) F x = (fun i => ((Fin.partialProd x i : T) : Γ6) • (1 : RationalGL3), F) from rfl]
  rw [prodMapHom_f_single]
  rfl

theorem flag_tensorHom_neg {X Y Z V : Rep.{0} ℚ Γ6} (f : X ⟶ Y) (g : Z ⟶ V) : f ⊗ₘ (-g) = -(f ⊗ₘ g) := by
  rw [eq_neg_iff_add_eq_zero, ← MonoidalPreadditive.tensor_add, neg_add_cancel]
  exact MonoidalPreadditive.tensor_zero _

theorem barCochain_add' {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (T : Subgroup Γ) (v₀ : V) (z : Z)
    {A : Rep.{0} ℚ Γ} {k : ℕ} (a b : (prodComplex Γ V Z).X k ⟶ A) (x : Fin k → T) :
    barCochain T v₀ z (a + b) x = barCochain T v₀ z a x + barCochain T v₀ z b x := rfl

theorem planeFlagCochain_bar (T : Subgroup Γ6) (F : Flag) (hF : ∀ g : T, g • F = F)
    (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) (w' : (prodComplex Γ6 RationalGL3 Flag).X 1 ⟶ W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (x : Fin 3 → T) :
    barCochain T (1 : RationalGL3) F (planeFlagCochain π z w' γ) x =
      cup21 ((W'.ρ).comp T.subtype) (pairOf π)
        (fun s t : T => barCochain T (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F) z
          (fun j : Fin 2 => if j = 0 then s else t))
        (fun s : T => barCochain T (1 : RationalGL3) F (-w') (fun _ : Fin 1 => s)) (x 0) (x 1) (x 2) +
      barCochain T (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F) γ x := by
  have h1 := diag21_bar T (1 : RationalGL3) F hF π (flagPlaneHom.hom.f 2 ≫ z) (-w') x
  unfold planeFlagCochain
  rw [barCochain_add', barCochain_flagPlane]
  congr 1
  refine Eq.trans h1 ?_
  exact congrArg (fun g => cup21 ((W'.ρ).comp T.subtype) (pairOf π) g
    (fun s : T => barCochain T (1 : RationalGL3) F (-w') (fun _ : Fin 1 => s)) (x 0) (x 1) (x 2))
    (funext fun s => funext fun t => barCochain_flagPlane T F z _)

theorem planeFlagCochain_d (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) :
    (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ planeFlagCochain π d.z e.w γ = 0 := by
  have L := (nerveDiagSystem Γ6 RationalGL3 Flag).leibniz 2 1 3 rfl
  have nat := nerveDelta_natural Γ6 RationalGL3 Flag SymmetricSpaceBoundaryFaceAugmentation.flagPlane
    SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant 2 2 4 rfl
  have nat' : flagPlaneHom.hom.f 4 ≫ (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl =
      (nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 2 4 rfl ≫ (flagPlaneHom.hom.f 2 ⊗ₘ flagPlaneHom.hom.f 2) := nat
  have hc : (prodComplex Γ6 RationalGL3 Flag).d 3 2 ≫ flagPlaneHom.hom.f 2 ≫ d.z = 0 := by
    have hcomm : (prodComplex Γ6 RationalGL3 Flag).d 3 2 ≫ flagPlaneHom.hom.f 2 =
        flagPlaneHom.hom.f 3 ≫ (prodComplex Γ6 RationalGL3 Plane).d 3 2 := (flagPlaneHom.hom.comm 3 2).symm
    rw [← Category.assoc, hcomm, Category.assoc, d.hz, comp_zero]
  have hcomm4 : (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ flagPlaneHom.hom.f 3 =
      flagPlaneHom.hom.f 4 ≫ (prodComplex Γ6 RationalGL3 Plane).d 4 3 := (flagPlaneHom.hom.comm 4 3).symm
  unfold planeFlagCochain
  rw [Preadditive.comp_add, ← Category.assoc, L]
  have h1 : (((prodComplex Γ6 RationalGL3 Flag).d (2 + 1) 2 ▷ (prodComplex Γ6 RationalGL3 Flag).X 1) ≫
        ((flagPlaneHom.hom.f 2 ≫ d.z) ⊗ₘ (-e.w))) = 0 := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
    have : (prodComplex Γ6 RationalGL3 Flag).d (2 + 1) 2 ≫ flagPlaneHom.hom.f 2 ≫ d.z = 0 := hc
    rw [this]
    exact MonoidalPreadditive.zero_tensor _
  have h2 : (((prodComplex Γ6 RationalGL3 Flag).X 2 ◁ (prodComplex Γ6 RationalGL3 Flag).d (1 + 1) 1) ≫
        ((flagPlaneHom.hom.f 2 ≫ d.z) ⊗ₘ (-e.w))) = -((flagPlaneHom.hom.f 2 ⊗ₘ flagPlaneHom.hom.f 2) ≫ (d.z ⊗ₘ e.z)) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Preadditive.comp_neg, e.hw,
      flag_tensorHom_neg, ← tensorHom_comp_tensorHom]
  have h1' := congrArg (fun a => a ≫ π) h1
  have h2' := congrArg (fun a => a ≫ π) h2
  simp only [Category.assoc, zero_comp, Preadditive.neg_comp] at h1' h2'
  rw [Preadditive.add_comp, Preadditive.zsmul_comp]
  simp only [Category.assoc]
  rw [h1', h2']
  have key : (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ flagPlaneHom.hom.f 3 ≫ γ =
      flagPlaneHom.hom.f 4 ≫ (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π := by
    rw [← Category.assoc, hcomm4, Category.assoc, hγ]
  have e : flagPlaneHom.hom.f 4 ≫ (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π =
      (nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 2 4 rfl ≫ (flagPlaneHom.hom.f 2 ⊗ₘ flagPlaneHom.hom.f 2) ≫ (d.z ⊗ₘ e.z) ≫ π := by
    rw [← Category.assoc, nat', Category.assoc]
  rw [key, e]
  simp

/-- **The Shapiro coordinate at a flag of the corner 3-cocycle of two plane data** is the class of the explicit cup cocycle
`x ↦ z̄(x₁, x₂) ⌣ (-w̄')(x₃) + γ̄(x₁, x₂, x₃)` of the flag stabilizer. -/
theorem planeFlag_faceCoord (F : Flag) (hF : ∀ g : MulAction.stabilizer Γ6 F, g • F = F)
    (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) (w' : (prodComplex Γ6 RationalGL3 Flag).X 1 ⟶ W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hθ : ((homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))).d (2 + 1) (2 + 1 + 1)).hom
      (planeFlagCochain π z w' γ) = 0) :
    ∃ hd : inhomogeneousCochains.d (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3
        (fun x : Fin 3 → MulAction.stabilizer Γ6 F =>
          cup21 ((W'.ρ).comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π)
            (fun s t : MulAction.stabilizer Γ6 F => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3)
              (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F) z (fun j : Fin 2 => if j = 0 then s else t))
            (fun s : MulAction.stabilizer Γ6 F => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F (-w') (fun _ : Fin 1 => s))
            (x 0) (x 1) (x 2) +
          barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F) γ x) = 0,
      (faceCoord (MulAction.stabilizer Γ6 F) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F hF 3).hom
          (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (planeFlagCochain π z w' γ) hθ) =
        (groupCohomology.π (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3).hom
          (groupCohomology.cocyclesMk _ hd) := by
  have hf : (fun x => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F (planeFlagCochain π z w' γ) x) =
      (fun x : Fin 3 → MulAction.stabilizer Γ6 F =>
          cup21 ((W'.ρ).comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π)
            (fun s t : MulAction.stabilizer Γ6 F => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3)
              (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F) z (fun j : Fin 2 => if j = 0 then s else t))
            (fun s : MulAction.stabilizer Γ6 F => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F (-w') (fun _ : Fin 1 => s))
            (x 0) (x 1) (x 2) +
          barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F) γ x) :=
    funext fun x => planeFlagCochain_bar π (MulAction.stabilizer Γ6 F) F hF z w' γ x
  have hd0 := barCochain_cocycle (MulAction.stabilizer Γ6 F) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F hF
    (planeFlagCochain π z w' γ) hθ
  rw [hf] at hd0
  refine ⟨hd0, ?_⟩
  refine (faceCoord_clsS_eq (MulAction.stabilizer Γ6 F) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F hF _ hθ).trans ?_
  exact congrArg (fun a => (groupCohomology.π (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3).hom a)
    (cocyclesMk_congr hf _ hd0)

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
