module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.BarClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.DiagCup12
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CornerAuto

@[expose] public section


/-!
# The corner 3-cocycle of two line data at a flag, and its class in the group cohomology of the flag stabilizer

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

`lineFlagCochain π w z' γ = Δ(w ⊗ z'|flags) ≫ π - γ|flags`, the flag 3-cochain of `LineDatum.conePair_exists_corner`.  For two line data `d`, `e` and a primitive `γ` of `d.z ∪ e.z` it is a cocycle of the
flag complex (`lineFlagCochain_d`, from the Leibniz rule of the model diagonal, `d.hw`, `e.hz` and naturality of the diagonal under `flagLineHom`), and its Shapiro coordinate at a flag `F` is the class
of the explicit inhomogeneous cocycle `x ↦ w̄(x₁) ⌣ z̄'(x₂, x₃) - γ̄(x₁, x₂, x₃)` of the flag stabilizer (`lineFlag_faceCoord`; the bar cochains are `barCochain` at the flag for `w`, at the line of the flag
for `z'`, `γ`).  This is the cochain-level form of the "local term" of the face factorisation: the evaluation functional of the corner chain acts on these classes (`corner_functional_decomp`).
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

/-- The flag 3-cochain `w ∪ (z'|flags) - γ|flags` of the corner evaluation of two line data. -/
def lineFlagCochain (w : (prodComplex Γ6 RationalGL3 Flag).X 1 ⟶ W) (z' : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) :
    (prodComplex Γ6 RationalGL3 Flag).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6) :=
  ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫ (w ⊗ₘ (flagLineHom.hom.f 2 ≫ z')) ≫ π) -
    flagLineHom.hom.f 3 ≫ γ

theorem barCochain_flagLine {k : ℕ} (T : Subgroup Γ6) (F : Flag) {A : Rep.{0} ℚ Γ6}
    (c : (prodComplex Γ6 RationalGL3 Line).X k ⟶ A) (x : Fin k → T) :
    barCochain T (1 : RationalGL3) F (flagLineHom.hom.f k ≫ c) x =
      barCochain T (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagLine F) c x := by
  unfold barCochain
  change c.hom (((flagLineHom.hom.f k)).hom (MonoidAlgebra.single _ 1)) = _
  rw [show barSimplex T (1 : RationalGL3) F x = (fun i => ((Fin.partialProd x i : T) : Γ6) • (1 : RationalGL3), F) from rfl]
  rw [prodMapHom_f_single]
  rfl

theorem barCochain_sub' {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (T : Subgroup Γ) (v₀ : V) (z : Z)
    {A : Rep.{0} ℚ Γ} {k : ℕ} (a b : (prodComplex Γ V Z).X k ⟶ A) (x : Fin k → T) :
    barCochain T v₀ z (a - b) x = barCochain T v₀ z a x - barCochain T v₀ z b x := rfl

theorem lineFlagCochain_bar (T : Subgroup Γ6) (F : Flag) (hF : ∀ g : T, g • F = F)
    (w : (prodComplex Γ6 RationalGL3 Flag).X 1 ⟶ W) (z' : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (x : Fin 3 → T) :
    barCochain T (1 : RationalGL3) F (lineFlagCochain π w z' γ) x =
      cup12 ((W'.ρ).comp T.subtype) (pairOf π)
        (fun s : T => barCochain T (1 : RationalGL3) F w (fun _ : Fin 1 => s))
        (fun s t : T => barCochain T (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagLine F) z'
          (fun j : Fin 2 => if j = 0 then s else t)) (x 0) (x 1) (x 2) -
      barCochain T (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagLine F) γ x := by
  have h1 := diag12_bar T (1 : RationalGL3) F hF π w (flagLineHom.hom.f 2 ≫ z') x
  unfold lineFlagCochain
  rw [barCochain_sub', barCochain_flagLine]
  congr 1
  refine Eq.trans h1 ?_
  exact congrArg (fun g => cup12 ((W'.ρ).comp T.subtype) (pairOf π)
    (fun s : T => barCochain T (1 : RationalGL3) F w (fun _ : Fin 1 => s)) g (x 0) (x 1) (x 2))
    (funext fun s => funext fun t => barCochain_flagLine T F z' _)

theorem cocyclesMk_congr {G : Type} [Group G] {A : Rep.{0} ℚ G} {n : ℕ} {f g : (Fin n → G) → A} (h : f = g)
    (hf : inhomogeneousCochains.d A n f = 0) (hg : inhomogeneousCochains.d A n g = 0) :
    groupCohomology.cocyclesMk f hf = groupCohomology.cocyclesMk g hg := by
  subst h
  rfl

/-- **The Shapiro coordinate at a flag of the corner 3-cocycle of two line data is the class of an explicit cup cocycle of the flag stabilizer**:
`x ↦ w̄(x₁) ⌣ z̄'(x₂, x₃) - γ̄(x₁, x₂, x₃)`, the bar cochains at the flag `F` (for `w`) and at its line (for `z'`, `γ`). -/
theorem lineFlag_faceCoord (F : Flag) (hF : ∀ g : MulAction.stabilizer Γ6 F, g • F = F)
    (w : (prodComplex Γ6 RationalGL3 Flag).X 1 ⟶ W) (z' : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hθ : ((homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))).d (2 + 1) (2 + 1 + 1)).hom
      (lineFlagCochain π w z' γ) = 0) :
    ∃ hd : inhomogeneousCochains.d (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3
        (fun x : Fin 3 → MulAction.stabilizer Γ6 F =>
          cup12 ((W'.ρ).comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π)
            (fun s : MulAction.stabilizer Γ6 F => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F w (fun _ : Fin 1 => s))
            (fun s t : MulAction.stabilizer Γ6 F => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3)
              (SymmetricSpaceBoundaryFaceAugmentation.flagLine F) z' (fun j : Fin 2 => if j = 0 then s else t)) (x 0) (x 1) (x 2) -
          barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagLine F) γ x) = 0,
      (faceCoord (MulAction.stabilizer Γ6 F) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F hF 3).hom
          (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (lineFlagCochain π w z' γ) hθ) =
        (groupCohomology.π (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3).hom
          (groupCohomology.cocyclesMk _ hd) := by
  have hf : (fun x => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F (lineFlagCochain π w z' γ) x) =
      (fun x : Fin 3 → MulAction.stabilizer Γ6 F =>
          cup12 ((W'.ρ).comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π)
            (fun s : MulAction.stabilizer Γ6 F => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F w (fun _ : Fin 1 => s))
            (fun s t : MulAction.stabilizer Γ6 F => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3)
              (SymmetricSpaceBoundaryFaceAugmentation.flagLine F) z' (fun j : Fin 2 => if j = 0 then s else t)) (x 0) (x 1) (x 2) -
          barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagLine F) γ x) :=
    funext fun x => lineFlagCochain_bar π (MulAction.stabilizer Γ6 F) F hF w z' γ x
  have hd0 := barCochain_cocycle (MulAction.stabilizer Γ6 F) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F hF
    (lineFlagCochain π w z' γ) hθ
  rw [hf] at hd0
  refine ⟨hd0, ?_⟩
  refine (faceCoord_clsS_eq (MulAction.stabilizer Γ6 F) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F hF _ hθ).trans ?_
  exact congrArg (fun a => (groupCohomology.π (Rep.res (MulAction.stabilizer Γ6 F).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3).hom a)
    (cocyclesMk_congr hf _ hd0)


theorem lineFlagCochain_d (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) :
    (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ lineFlagCochain π d.w e.z γ = 0 := by
  have L := (nerveDiagSystem Γ6 RationalGL3 Flag).leibniz 1 2 3 rfl
  have nat := nerveDelta_natural Γ6 RationalGL3 Flag SymmetricSpaceBoundaryFaceAugmentation.flagLine
    SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant 2 2 4 rfl
  have hc : (prodComplex Γ6 RationalGL3 Flag).d 3 2 ≫ flagLineHom.hom.f 2 ≫ e.z = 0 := by
    have hcomm : (prodComplex Γ6 RationalGL3 Flag).d 3 2 ≫ flagLineHom.hom.f 2 =
        flagLineHom.hom.f 3 ≫ (prodComplex Γ6 RationalGL3 Line).d 3 2 := (flagLineHom.hom.comm 3 2).symm
    rw [← Category.assoc, hcomm, Category.assoc, e.hz, comp_zero]
  unfold lineFlagCochain
  rw [Preadditive.comp_sub, ← Category.assoc, L]
  have hcomm4 : (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ flagLineHom.hom.f 3 =
      flagLineHom.hom.f 4 ≫ (prodComplex Γ6 RationalGL3 Line).d 4 3 := (flagLineHom.hom.comm 4 3).symm
  have h1 : (((prodComplex Γ6 RationalGL3 Flag).d (1 + 1) 1 ▷ (prodComplex Γ6 RationalGL3 Flag).X 2) ≫
        (d.w ⊗ₘ (flagLineHom.hom.f 2 ≫ e.z))) = (flagLineHom.hom.f 2 ⊗ₘ flagLineHom.hom.f 2) ≫ (d.z ⊗ₘ e.z) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, tensorHom_comp_tensorHom]
    exact congrArg (fun a => a ⊗ₘ (flagLineHom.hom.f 2 ≫ e.z)) d.hw
  have h2 : (((prodComplex Γ6 RationalGL3 Flag).X 1 ◁ (prodComplex Γ6 RationalGL3 Flag).d (2 + 1) 2) ≫
        (d.w ⊗ₘ (flagLineHom.hom.f 2 ≫ e.z))) = 0 := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
    have : (prodComplex Γ6 RationalGL3 Flag).d (2 + 1) 2 ≫ flagLineHom.hom.f 2 ≫ e.z = 0 := hc
    rw [this]
    exact MonoidalPreadditive.tensor_zero _
  have h1' := congrArg (fun a => a ≫ π) h1
  have h2' := congrArg (fun a => a ≫ π) h2
  simp only [Category.assoc, zero_comp] at h1' h2'
  rw [Preadditive.add_comp, Preadditive.zsmul_comp]
  simp only [Category.assoc]
  rw [h1', h2']
  have nat' : flagLineHom.hom.f 4 ≫ (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl =
      (nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 2 4 rfl ≫ (flagLineHom.hom.f 2 ⊗ₘ flagLineHom.hom.f 2) := nat
  have key : (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ flagLineHom.hom.f 3 ≫ γ =
      flagLineHom.hom.f 4 ≫ (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π := by
    rw [← Category.assoc, hcomm4, Category.assoc, hγ]
  have e : flagLineHom.hom.f 4 ≫ (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π =
      (nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 2 4 rfl ≫ (flagLineHom.hom.f 2 ⊗ₘ flagLineHom.hom.f 2) ≫ (d.z ⊗ₘ e.z) ≫ π := by
    rw [← Category.assoc, nat', Category.assoc]
  rw [key, e, comp_zero, smul_zero]
  simp


end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
