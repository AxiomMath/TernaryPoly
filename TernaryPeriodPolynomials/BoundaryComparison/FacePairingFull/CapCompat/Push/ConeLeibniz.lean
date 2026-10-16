module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeDiag

@[expose] public section


/-!
# The Leibniz rule for the diagonal of a pushout cone

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

theorem neg_one_pow_sq' (k : ℕ) : ((-1 : ℤ)^k) * ((-1 : ℤ)^k) = 1 := by
  rw [← mul_pow]; norm_num

section Tensor

variable {X Y Z W : Rep.{0} ℚ Γ}

theorem tensorHom_whiskerRight' {X' Y' Z' W' : Rep.{0} ℚ Γ} (f : X' ⟶ Y') (g : Z' ⟶ W') (h : Y' ⟶ X) :
    (f ⊗ₘ g) ≫ (h ▷ W') = (f ≫ h) ⊗ₘ g := by
  rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

theorem tensorHom_whiskerLeft' {X' Y' Z' W' : Rep.{0} ℚ Γ} (f : X' ⟶ Y') (g : Z' ⟶ W') (h : W' ⟶ X) :
    (f ⊗ₘ g) ≫ (Y' ◁ h) = f ⊗ₘ (g ≫ h) := by
  rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

theorem whiskerRight_tensorHom' {X' Y' Z' W' : Rep.{0} ℚ Γ} (h : X ⟶ X') (f : X' ⟶ Y') (g : Z' ⟶ W') :
    (h ▷ Z') ≫ (f ⊗ₘ g) = (h ≫ f) ⊗ₘ g := by
  rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

theorem whiskerLeft_tensorHom' {X' Y' Z' W' : Rep.{0} ℚ Γ} (h : Z ⟶ Z') (f : X' ⟶ Y') (g : Z' ⟶ W') :
    (X' ◁ h) ≫ (f ⊗ₘ g) = f ⊗ₘ (h ≫ g) := by
  rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

theorem neg_tensorHom' {X' Y' Z' W' : Rep.{0} ℚ Γ} (f : X' ⟶ Y') (h : Z' ⟶ W') :
    (-f) ⊗ₘ h = -(f ⊗ₘ h) := by
  rw [eq_neg_iff_add_eq_zero, ← MonoidalPreadditive.add_tensor, neg_add_cancel, MonoidalPreadditive.zero_tensor]

theorem tensorHom_neg' {X' Y' Z' W' : Rep.{0} ℚ Γ} (f : X' ⟶ Y') (h : Z' ⟶ W') :
    f ⊗ₘ (-h) = -(f ⊗ₘ h) := by
  rw [eq_neg_iff_add_eq_zero, ← MonoidalPreadditive.tensor_add, neg_add_cancel, MonoidalPreadditive.tensor_zero]

theorem sub_tensorHom' {X' Y' Z' W' : Rep.{0} ℚ Γ} (f g : X' ⟶ Y') (h : Z' ⟶ W') :
    (f - g) ⊗ₘ h = f ⊗ₘ h - g ⊗ₘ h := by
  rw [sub_eq_add_neg, MonoidalPreadditive.add_tensor, neg_tensorHom', ← sub_eq_add_neg]

theorem tensorHom_sub' {X' Y' Z' W' : Rep.{0} ℚ Γ} (f : X' ⟶ Y') (g h : Z' ⟶ W') :
    f ⊗ₘ (g - h) = f ⊗ₘ g - f ⊗ₘ h := by
  rw [sub_eq_add_neg, MonoidalPreadditive.tensor_add, tensorHom_neg', ← sub_eq_add_neg]

end Tensor

namespace PushCone

variable {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  (𝒞 : PushCone A L P K a b) (SA : DiagSystem A) (SL : DiagSystem L) (SP : DiagSystem P)

theorem leibniz_L (p q n : ℕ) (h : p + q = n) :
    𝒞.iL (n+1) ≫ (K.d (n+1) n ≫ 𝒞.Δ SA SL SP p q n h) =
      𝒞.iL (n+1) ≫ (𝒞.Δ SA SL SP (p+1) q (n+1) (by omega) ≫ (K.d (p+1) p ▷ K.X q) +
        ((-1 : ℤ)^p) • (𝒞.Δ SA SL SP p (q+1) (n+1) (by omega) ≫ (K.X p ◁ K.d (q+1) q))) := by
  rw [← Category.assoc, 𝒞.dL, Category.assoc, iL_Δ' (𝒞 := 𝒞) (SA := SA) (SP := SP), Preadditive.comp_add,
    Preadditive.comp_zsmul, ← Category.assoc (𝒞.iL (n+1)), ← Category.assoc (𝒞.iL (n+1)),
    iL_Δ' (𝒞 := 𝒞) (SA := SA) (SP := SP), iL_Δ' (𝒞 := 𝒞) (SA := SA) (SP := SP)]
  simp only [Category.assoc]
  rw [tensorHom_whiskerRight', tensorHom_whiskerLeft', 𝒞.dL p, 𝒞.dL q, ← Category.assoc, SL.leibniz p q n h,
    Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, Category.assoc, whiskerRight_tensorHom',
    whiskerLeft_tensorHom']

theorem leibniz_P (p q n : ℕ) (h : p + q = n) :
    𝒞.iP (n+1) ≫ (K.d (n+1) n ≫ 𝒞.Δ SA SL SP p q n h) =
      𝒞.iP (n+1) ≫ (𝒞.Δ SA SL SP (p+1) q (n+1) (by omega) ≫ (K.d (p+1) p ▷ K.X q) +
        ((-1 : ℤ)^p) • (𝒞.Δ SA SL SP p (q+1) (n+1) (by omega) ≫ (K.X p ◁ K.d (q+1) q))) := by
  rw [← Category.assoc, 𝒞.dP, Category.assoc, iP_Δ' (𝒞 := 𝒞) (SA := SA) (SL := SL), Preadditive.comp_add,
    Preadditive.comp_zsmul, ← Category.assoc (𝒞.iP (n+1)), ← Category.assoc (𝒞.iP (n+1)),
    iP_Δ' (𝒞 := 𝒞) (SA := SA) (SL := SL), iP_Δ' (𝒞 := 𝒞) (SA := SA) (SL := SL)]
  simp only [Category.assoc]
  rw [tensorHom_whiskerRight', tensorHom_whiskerLeft', 𝒞.dP p, 𝒞.dP q, ← Category.assoc, SP.leibniz p q n h,
    Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, Category.assoc, whiskerRight_tensorHom',
    whiskerLeft_tensorHom']

theorem leibniz_A_SS (hS : Strict (a := a) (b := b) SA SL SP) (p' q' m : ℕ) (h : p' + 1 + (q' + 1) = m + 1) :
    𝒞.iA (m+1) ≫ (K.d (m+2) (m+1) ≫ 𝒞.Δ SA SL SP (p'+1) (q'+1) (m+1) h) =
      𝒞.iA (m+1) ≫ (𝒞.Δ SA SL SP (p'+1+1) (q'+1) (m+1+1) (by omega) ≫ (K.d (p'+1+1) (p'+1) ▷ K.X (q'+1)) +
        ((-1 : ℤ)^(p'+1)) • (𝒞.Δ SA SL SP (p'+1) (q'+1+1) (m+1+1) (by omega) ≫
          (K.X (p'+1) ◁ K.d (q'+1+1) (q'+1)))) := by
  rw [← Category.assoc, 𝒞.dA m]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc,
    𝒞.iA_Δ_assoc SA SL SP, 𝒞.iA_Δ SA SL SP, 𝒞.iL_Δ SA SL SP, 𝒞.iP_Δ SA SL SP, Preadditive.comp_add,
    Preadditive.comp_zsmul]
  simp only [PushCone.aPart, PushCone.tIc, PushCone.tIIc, PushCone.tI, PushCone.tII, Preadditive.comp_add,
    Preadditive.add_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Category.assoc, tensorHom_whiskerRight', tensorHom_whiskerLeft']
  have hAL1 := reassoc_of% (SA.leibniz p' (q'+1) m (by omega))
  have hAL2 := reassoc_of% (SA.leibniz (p'+1) q' m (by omega))
  have hsa := reassoc_of% (hS.a_strict (p'+1) (q'+1) (m+1) h)
  have hsb := reassoc_of% (hS.b_strict (p'+1) (q'+1) (m+1) h)
  rw [hAL1, hAL2, hsa, hsb]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, whiskerRight_tensorHom',
    whiskerLeft_tensorHom', MonoidalCategory.tensorHom_comp_tensorHom]
  rw [𝒞.dA p', 𝒞.dP (p'+1), 𝒞.dL (q'+1), 𝒞.dA q', ← Category.assoc (b.f (p'+1+1)), b.comm (p'+1+1) (p'+1),
    ← Category.assoc (a.f (q'+1+1)), a.comm (q'+1+1) (q'+1)]
  simp only [Category.assoc, sub_tensorHom', tensorHom_sub', neg_tensorHom', tensorHom_neg',
    MonoidalPreadditive.add_tensor, MonoidalPreadditive.tensor_add, Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.comp_neg, smul_add, smul_sub, smul_neg, smul_smul]
  clear hAL1 hAL2 hsa hsb
  match_scalars <;> first | ring1 | (rw [neg_one_pow_sq']; all_goals ring1)

theorem leibniz_A_00 (hS : Strict (a := a) (b := b) SA SL SP) (h : 0 + 0 = 0) :
    𝒞.iA 0 ≫ (K.d 1 0 ≫ 𝒞.Δ SA SL SP 0 0 0 h) =
      𝒞.iA 0 ≫ (𝒞.Δ SA SL SP (0+1) 0 (0+1) (by omega) ≫ (K.d (0+1) 0 ▷ K.X 0) +
        ((-1 : ℤ)^0) • (𝒞.Δ SA SL SP 0 (0+1) (0+1) (by omega) ≫ (K.X 0 ◁ K.d (0+1) 0))) := by
  rw [← Category.assoc, 𝒞.dA0]
  have hsa := reassoc_of% (hS.a_strict 0 0 0 h)
  have hsb := reassoc_of% (hS.b_strict 0 0 0 h)
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc, 𝒞.iA_Δ_assoc SA SL SP,
    iL_Δ_zero, iP_Δ_zero, Preadditive.comp_add, Preadditive.comp_zsmul,
    PushCone.aPart, PushCone.tIc, PushCone.tIIc, PushCone.tI, PushCone.tII, Preadditive.zsmul_comp,
    tensorHom_whiskerRight', tensorHom_whiskerLeft']
  rw [hsa, hsb, 𝒞.dA0]
  simp only [sub_tensorHom', tensorHom_sub', MonoidalCategory.tensorHom_comp_tensorHom,
    zero_comp, smul_zero, zero_add, add_zero, Preadditive.comp_sub, smul_sub]
  clear hsa hsb
  match_scalars <;> ring1

theorem leibniz_A_S0 (hS : Strict (a := a) (b := b) SA SL SP) (p' m : ℕ) (h : p' + 1 + 0 = m + 1) :
    𝒞.iA (m+1) ≫ (K.d (m+2) (m+1) ≫ 𝒞.Δ SA SL SP (p'+1) 0 (m+1) h) =
      𝒞.iA (m+1) ≫ (𝒞.Δ SA SL SP (p'+1+1) 0 (m+1+1) (by omega) ≫ (K.d (p'+1+1) (p'+1) ▷ K.X 0) +
        ((-1 : ℤ)^(p'+1)) • (𝒞.Δ SA SL SP (p'+1) (0+1) (m+1+1) (by omega) ≫
          (K.X (p'+1) ◁ K.d (0+1) 0))) := by
  rw [← Category.assoc, 𝒞.dA m]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc,
    𝒞.iA_Δ_assoc SA SL SP, 𝒞.iA_Δ SA SL SP, 𝒞.iL_Δ SA SL SP, 𝒞.iP_Δ SA SL SP, Preadditive.comp_add,
    Preadditive.comp_zsmul]
  simp only [PushCone.aPart, PushCone.tIc, PushCone.tIIc, PushCone.tI, PushCone.tII, Preadditive.comp_add,
    Preadditive.add_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Category.assoc, tensorHom_whiskerRight', tensorHom_whiskerLeft']
  have hAL1 := reassoc_of% (SA.leibniz p' 0 m (by omega))
  have hsa := reassoc_of% (hS.a_strict (p'+1) 0 (m+1) h)
  have hsb := reassoc_of% (hS.b_strict (p'+1) 0 (m+1) h)
  rw [hAL1, hsa, hsb]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, whiskerRight_tensorHom',
    whiskerLeft_tensorHom', MonoidalCategory.tensorHom_comp_tensorHom, comp_zero, zero_comp, smul_zero,
    add_zero]
  rw [𝒞.dA p', 𝒞.dL 0, 𝒞.dA0, ← Category.assoc (a.f (0+1)), a.comm (0+1) 0]
  simp only [Category.assoc, sub_tensorHom', tensorHom_sub', neg_tensorHom',
    MonoidalPreadditive.add_tensor, Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.comp_neg, smul_add, smul_sub, smul_smul]
  clear hAL1 hsa hsb
  match_scalars <;> first | ring1 | (rw [neg_one_pow_sq']; all_goals ring1)

theorem leibniz_A_0S (hS : Strict (a := a) (b := b) SA SL SP) (q' m : ℕ) (h : 0 + (q' + 1) = m + 1) :
    𝒞.iA (m+1) ≫ (K.d (m+2) (m+1) ≫ 𝒞.Δ SA SL SP 0 (q'+1) (m+1) h) =
      𝒞.iA (m+1) ≫ (𝒞.Δ SA SL SP (0+1) (q'+1) (m+1+1) (by omega) ≫ (K.d (0+1) 0 ▷ K.X (q'+1)) +
        ((-1 : ℤ)^0) • (𝒞.Δ SA SL SP 0 (q'+1+1) (m+1+1) (by omega) ≫
          (K.X 0 ◁ K.d (q'+1+1) (q'+1)))) := by
  rw [← Category.assoc, 𝒞.dA m]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc,
    𝒞.iA_Δ_assoc SA SL SP, 𝒞.iA_Δ SA SL SP, 𝒞.iL_Δ SA SL SP, 𝒞.iP_Δ SA SL SP, Preadditive.comp_add,
    Preadditive.comp_zsmul]
  simp only [PushCone.aPart, PushCone.tIc, PushCone.tIIc, PushCone.tI, PushCone.tII, Preadditive.comp_add,
    Preadditive.add_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Category.assoc, tensorHom_whiskerRight', tensorHom_whiskerLeft']
  have hAL2 := reassoc_of% (SA.leibniz 0 q' m (by omega))
  have hsa := reassoc_of% (hS.a_strict 0 (q'+1) (m+1) h)
  have hsb := reassoc_of% (hS.b_strict 0 (q'+1) (m+1) h)
  rw [hAL2, hsa, hsb]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, whiskerRight_tensorHom',
    whiskerLeft_tensorHom', MonoidalCategory.tensorHom_comp_tensorHom, comp_zero, zero_comp, zero_add]
  rw [𝒞.dA0, 𝒞.dP 0, ← Category.assoc (b.f (0+1)), b.comm (0+1) 0, 𝒞.dA q']
  simp only [Category.assoc, sub_tensorHom', tensorHom_sub', tensorHom_neg',
    MonoidalPreadditive.tensor_add, Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.comp_neg, smul_add, smul_sub, smul_neg, smul_smul]
  clear hAL2 hsa hsb
  match_scalars <;> ring1

theorem leibniz (hS : Strict (a := a) (b := b) SA SL SP) (p q n : ℕ) (h : p + q = n) :
    K.d (n+1) n ≫ 𝒞.Δ SA SL SP p q n h =
      𝒞.Δ SA SL SP (p+1) q (n+1) (by omega) ≫ (K.d (p+1) p ▷ K.X q) +
        ((-1 : ℤ)^p) • (𝒞.Δ SA SL SP p (q+1) (n+1) (by omega) ≫ (K.X p ◁ K.d (q+1) q)) := by
  apply 𝒞.ext n
  · rcases p with _ | p' <;> rcases q with _ | q'
    · obtain rfl : n = 0 := by omega
      exact 𝒞.leibniz_A_00 SA SL SP hS h
    · obtain rfl : n = q' + 1 := by omega
      exact 𝒞.leibniz_A_0S SA SL SP hS q' q' h
    · obtain rfl : n = p' + 1 := by omega
      exact 𝒞.leibniz_A_S0 SA SL SP hS p' p' h
    · obtain rfl : n = (p' + q' + 1) + 1 := by omega
      exact 𝒞.leibniz_A_SS SA SL SP hS p' q' (p' + q' + 1) h
  · exact 𝒞.leibniz_L SA SL SP p q n h
  · exact 𝒞.leibniz_P SA SL SP p q n h

/-- The diagonal system of the pushout cone. -/
def diagSystem (hS : Strict (a := a) (b := b) SA SL SP) : DiagSystem K where
  Δ := 𝒞.Δ SA SL SP
  leibniz := 𝒞.leibniz SA SL SP hS
  eps := 𝒞.eps SL SP
  eps_d := 𝒞.eps_d hS
  counit := 𝒞.counit hS

end PushCone

/-- The diagonal system of the homotopy pushout cone of two strictly diagonal-compatible chain maps. -/
def pushConeDiagSystem {A L P : ChainComplex (Rep.{0} ℚ Γ) ℕ} (a : A ⟶ L) (b : A ⟶ P) (SA : DiagSystem A)
    (SL : DiagSystem L) (SP : DiagSystem P) (hS : PushCone.Strict (a := a) (b := b) SA SL SP) :
    DiagSystem (pushCone a b) :=
  (pushConeOfCofiber a b).diagSystem SA SL SP hS

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
