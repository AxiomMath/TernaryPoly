module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Tree.MapsLin
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Tree.MapsEdge
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Face.Main

@[expose] public section


/-!
# Lemma B.1: the tree maps `t₃`, `t₂`, the data `treeData`, and the literal `PHCompat n`

Formalized by Claude Sonnet 5.5.

`t₂ : L ⊗ Res P0 → Φ(RG₂)` sends `ℓ ⊗ [t]` to `ℓ · F2 t` (the class of the hexagon over the Farey triangle `t`) and
`t₃ : L ⊗ Res P1 → Φ(RG₃)` sends `ℓ ⊗ c` to `ℓ · F3lin c` (the class of the top cells over the oriented edges), for the
determinant line `L = Ldet`.  They are `P_H/U`-equivariant (`F2lin_equiv`, `F3lin_equiv`), commute with the boundaries
(`dPhi_F3lin`, `F2_boundary`), and `t₂(ℓ₀ ⊗ s₀)` is not a boundary because the functional `ψ` of `exists_psi` takes the value
`ε(s₀) = 1` on it.  The resulting `treeData : TreeData` gives `PHCompat n` for all `n` by `phCompat_of_tree`.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames

/-- `ℓ ⊗ m ↦ ℓ • f m` on `ℚ ⊗ M`. -/
def ttLin {M N : Type} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N] (f : M →ₗ[ℚ] N) :
    TensorProduct ℚ ℚ M →ₗ[ℚ] N :=
  (TensorProduct.lid ℚ N).toLinearMap ∘ₗ LinearMap.lTensor ℚ f

theorem ttLin_tmul {M N : Type} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N] (f : M →ₗ[ℚ] N)
    (a : ℚ) (m : M) : ttLin f (a ⊗ₜ[ℚ] m) = a • f m := by
  simp [ttLin]

/-- The underlying rational number of an element of `Ldet`. -/
def lv (a : Ldet.V) : ℚ := a

/-- The element `1` of the line `Ldet`. -/
def lone : Ldet.V := (1 : ℚ)

theorem lv_lone : lv lone = 1 := rfl

/-- The representation `L ⊗ Res P1`. -/
abbrev LP1 : Rep.{0} ℚ (PH ⧸ U) := Ldet ⊗ Rep.res pibar P1

/-- The representation `L ⊗ Res P0`. -/
abbrev LP0 : Rep.{0} ℚ (PH ⧸ U) := Ldet ⊗ Rep.res pibar P0

/-- The linear map underlying `t₃`. -/
def t3Lin : Ldet.V ⊗[ℚ] (Rep.res pibar P1).V →ₗ[ℚ] (PhiX 3).V :=
  ttLin (M := ↥antiSub) (F3lin ∘ₗ antiSub.subtype)

/-- The linear map underlying `t₂`. -/
def t2Lin : Ldet.V ⊗[ℚ] (Rep.res pibar P0).V →ₗ[ℚ] (PhiX 2).V :=
  ttLin (M := P0.V) F2lin

theorem t3Lin_tmul a (c : (Rep.res pibar P1).V) :
    t3Lin (a ⊗ₜ[ℚ] c) = lv a • F3lin (c : PE.V) :=
  ttLin_tmul (M := ↥antiSub) (F3lin ∘ₗ antiSub.subtype) (lv a) c

theorem t2Lin_tmul a (c : (Rep.res pibar P0).V) :
    t2Lin (a ⊗ₜ[ℚ] c) = lv a • F2lin (c : P0.V) :=
  ttLin_tmul (M := P0.V) F2lin (lv a) c

theorem t3Lin_equiv (q : PH ⧸ U) (x : Ldet.V ⊗[ℚ] (Rep.res pibar P1).V) :
    t3Lin (LP1.ρ q x) = (PhiX 3).ρ q (t3Lin x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    have e : LP1.ρ q (a ⊗ₜ[ℚ] c) =
        Ldet.ρ q a ⊗ₜ[ℚ] (Rep.res pibar P1).ρ q c := by simp
    rw [e, t3Lin_tmul, t3Lin_tmul]
    have h := detQ_mul_self q
    change (detQ q • lv a) • F3lin (PE.ρ (pibar q) (c : PE.V)) =
      (PhiX 3).ρ q (lv a • F3lin (c : PE.V))
    rw [F3lin_equiv, map_smul ((PhiX 3).ρ q) (lv a) (F3lin (c : PE.V)), smul_smul, smul_eq_mul]
    congr 1
    calc detQ q * lv a * detQ q = lv a * (detQ q * detQ q) := by ring
      _ = lv a := by rw [h, mul_one]

theorem t2Lin_equiv (q : PH ⧸ U) (x : Ldet.V ⊗[ℚ] (Rep.res pibar P0).V) :
    t2Lin (LP0.ρ q x) = (PhiX 2).ρ q (t2Lin x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    have e : LP0.ρ q (a ⊗ₜ[ℚ] c) =
        Ldet.ρ q a ⊗ₜ[ℚ] (Rep.res pibar P0).ρ q c := by simp
    rw [e, t2Lin_tmul, t2Lin_tmul]
    have h := detQ_mul_self q
    change (detQ q • lv a) • F2lin (P0.ρ (pibar q) (c : P0.V)) =
      (PhiX 2).ρ q (lv a • F2lin (c : P0.V))
    rw [F2lin_equiv, map_smul ((PhiX 2).ρ q) (lv a) (F2lin (c : P0.V)), smul_smul, smul_eq_mul]
    congr 1
    calc detQ q * lv a * detQ q = lv a * (detQ q * detQ q) := by ring
      _ = lv a := by rw [h, mul_one]

/-- The tree map `t₃ : L ⊗ Res P1 → Φ(RG₃)`. -/
def t3 : Ldet ⊗ Rep.res pibar P1 ⟶ (Phi U).obj ((RG_projRes PH).complex.X 3) :=
  Rep.ofHom ⟨t3Lin, fun q => LinearMap.ext (t3Lin_equiv q)⟩

/-- The tree map `t₂ : L ⊗ Res P0 → Φ(RG₂)`. -/
def t2 : Ldet ⊗ Rep.res pibar P0 ⟶ (Phi U).obj ((RG_projRes PH).complex.X 2) :=
  Rep.ofHom ⟨t2Lin, fun q => LinearMap.ext (t2Lin_equiv q)⟩

theorem t3_hom (x : Ldet.V ⊗[ℚ] (Rep.res pibar P1).V) : t3.hom x = t3Lin x := rfl

theorem t2_hom (x : Ldet.V ⊗[ℚ] (Rep.res pibar P0).V) : t2.hom x = t2Lin x := rfl

theorem Phi_d_32 : (Phi U).map ((RG_projRes PH).complex.d 3 2) = dPhi 2 :=
  congrArg (Phi U).map (RGH_d PH 2)

theorem Phi_d_21 : (Phi U).map ((RG_projRes PH).complex.d 2 1) =
    (Phi U).map ((Rep.resFunctor PH.subtype).map (dRG 1)) :=
  congrArg (Phi U).map (RGH_d PH 1)

theorem tree_hi : t3 ≫ (Phi U).map ((RG_projRes PH).complex.d 3 2) = (Ldet ◁ Rep.resMap pibar d1) ≫ t2 := by
  rw [Phi_d_32]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    change (dPhi 2).hom (t3Lin (a ⊗ₜ[ℚ] c)) = t2Lin (a ⊗ₜ[ℚ] d1.hom c)
    rw [t3Lin_tmul, t2Lin_tmul, map_smul, dPhi_F3lin]
    rfl

theorem tree_hii : t2 ≫ (Phi U).map ((RG_projRes PH).complex.d 2 1) = 0 := by
  rw [Phi_d_21]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    change ((Phi U).map ((Rep.resFunctor PH.subtype).map (dRG 1))).hom (t2Lin (a ⊗ₜ[ℚ] c)) = 0
    rw [t2Lin_tmul, map_smul, dPhi1_F2lin, smul_zero]

/-- The chosen preimage of `1` under the augmentation. -/
abbrev sZ0 : P0.V := sZero (Rep.res pibar P1) (Rep.res pibar P0) (Rep.resMap pibar d1)
  (epsQ pibar) (resD1_epsQ pibar) (sesQ_shortExact pibar)

theorem tree_h3 : t2.hom (lone ⊗ₜ[ℚ] sZ0) ∉
    LinearMap.range ((Phi U).map ((RG_projRes PH).complex.d 3 2)).hom.toLinearMap := by
  obtain ⟨ψ, hψ0, hψ1⟩ := exists_psi
  rintro ⟨x, hx⟩
  have hs := sZero_spec (Rep.res pibar P1) (Rep.res pibar P0) (Rep.resMap pibar d1)
    (epsQ pibar) (resD1_epsQ pibar) (sesQ_shortExact pibar)
  change (dPhi 2).hom x = t2Lin (lone ⊗ₜ[ℚ] sZ0) at hx
  rw [t2Lin_tmul, lv_lone, one_smul] at hx
  have h1 : ψ ((dPhi 2).hom x) = 1 := by
    rw [hx, psi_F2lin ψ hψ1]
    exact hs
  rw [hψ0 x] at h1
  exact zero_ne_one h1

theorem tree_ht3 : t3.hom (lone ⊗ₜ[ℚ] edgeGen) =
    Coinvariants.mk (((RG_projRes PH).complex.X 3).ρ.comp U.subtype) genT0 := by
  have h : F3lin (edgeGen : PE.V) = F3 p0 := by
    rw [edgeGen_coe]
    unfold edgeVec
    rw [map_smul, map_sub, F3lin_single, F3lin_single, F3_smul_swap, one_smul, one_smul]
    module
  change t3Lin (lone ⊗ₜ[ℚ] edgeGen) = _
  rw [t3Lin_tmul, lv_lone, one_smul, h]
  exact F3_p0_genT0

/-- **The tree data of Lemma B.1**, constructed from the oriented cell resolution: `L` is the determinant line of
`P_H/U`, `t₂`, `t₃` the maps `ℓ ⊗ t ↦ ℓ F2 t`, `ℓ ⊗ e ↦ ℓ F3 e`. -/
def treeData : TreeData where
  L := Ldet
  ℓ₀ := lone
  hℓ := (by norm_num : (1 : ℚ) ≠ 0)
  hL := Module.finrank_self ℚ
  t3 := t3
  t2 := t2
  hi := tree_hi
  hii := tree_hii
  h3 := tree_h3
  ht3 := tree_ht3

/-- **Lemma B.1, the literal residue comparison**: `PHCompat n` for every `n`. -/
theorem phCompat_literal (n : ℕ) : PHCompat n := phCompat_of_tree treeData n

theorem faceEvalAvg_literal (n : ℕ) : FaceEvalAvg n := faceEvalAvg_of_tree treeData n

end TernaryPeriodPolynomials.Argument.AppendixBResidue
