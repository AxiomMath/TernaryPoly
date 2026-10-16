module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.TensorCarriers

@[expose] public section


/-!
# Cap compatibility of carried chain maps

Let `u : C ⟶ D` be a chain map of complexes of representations with cap systems, where `C` has a free `Γ`-cell basis
`B` and `D` carries acyclic carriers `𝒦` indexed by the cells of `C`.  If `u` is carried, preserves the augmentations,
and both cap systems respect the carriers, then for every cocycle `b` of `D`

  `(cap_C (u ≫ b) ≫ (W ◁ u))  ≃  (u ≫ cap_D b)`

by a homotopy carried by the tensor carriers `W ⊗ K` (`cap_compat`).  Evaluating on cycles gives the equality of the
Kronecker pairings (`CapCompat.Evaluation`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory TensorProduct
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ] {C D : ChainComplex (Rep.{0} ℚ Γ) ℕ}

theorem neg_one_pow_mul_self (a : ℕ) : ((-1 : ℤ)^a) * ((-1 : ℤ)^a) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

/-- The Leibniz rule in the form used for the homotopy. -/
theorem CapSystem.intertwine' (S : CapSystem C) {W : Rep.{0} ℚ Γ} {a : ℕ} (b : C.X a ⟶ W)
    (hb : C.d (a+1) a ≫ b = 0) (q : ℕ) :
    S.cap b hb (q+1) ≫ (W ◁ C.d (q+1) q) = ((-1 : ℤ)^a) • (C.d (a+q+1) (a+q) ≫ S.cap b hb q) := by
  rw [S.intertwine b hb q, smul_smul, neg_one_pow_mul_self, one_smul]

theorem chainMap_cocycle (u : C ⟶ D) {W : Rep.{0} ℚ Γ} {a : ℕ} (b : D.X a ⟶ W) (hb : D.d (a+1) a ≫ b = 0) :
    C.d (a+1) a ≫ (u.f a ≫ b) = 0 := by
  rw [← Category.assoc, ← u.comm, Category.assoc, hb, comp_zero]

/-- The caps of the cells of `C` are carried by smaller carriers. -/
def CapCellCarried {B : CellBasis C} (SC : CapSystem C) (𝒦 : CarrierData B D) : Prop :=
  ∀ {W : Rep.{0} ℚ Γ} {a : ℕ} (b : C.X a ⟶ W) (hb : C.d (a+1) a ≫ b = 0) (q : ℕ) (s : B.S (a+q)),
    (SC.cap b hb q).hom (B.cell (a+q) s) ∈ Submodule.span ℚ
      {x | ∃ (w : W) (t : B.S q), (∀ m, 𝒦.K q t m ≤ 𝒦.K (a+q) s m) ∧
        x = (w ⊗ₜ[ℚ] B.cell q t : (W ⊗ C.X q : Rep.{0} ℚ Γ))}

/-- The caps of `D` preserve the carriers (tensored with the coefficient representation). -/
def CapCarrierPreserved {B : CellBasis C} (SD : CapSystem D) (𝒦 : CarrierData B D) : Prop :=
  ∀ {W : Rep.{0} ℚ Γ} {a : ℕ} (b : D.X a ⟶ W) (hb : D.d (a+1) a ≫ b = 0) (q : ℕ) (n : ℕ) (s : B.S n)
    (x : D.X (a+q)), x ∈ 𝒦.K n s (a+q) → (SD.cap b hb q).hom x ∈ tensorK W (𝒦.K n s q)

theorem cap_f_twisted (SC : CapSystem C) (u : C ⟶ D) {W : Rep.{0} ℚ Γ} {a : ℕ} (b : D.X a ⟶ W)
    (hb : D.d (a+1) a ≫ b = 0) (q : ℕ) :
    (SC.cap (u.f a ≫ b) (chainMap_cocycle u b hb) (q+1) ≫ (W ◁ u.f (q+1))) ≫ (W ◁ D.d (q+1) q) =
      ((-1 : ℤ)^a) • (C.d (a+q+1) (a+q) ≫ (SC.cap (u.f a ≫ b) (chainMap_cocycle u b hb) q ≫ (W ◁ u.f q))) := by
  rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, u.comm, MonoidalCategory.whiskerLeft_comp,
    ← Category.assoc, SC.intertwine', Preadditive.zsmul_comp, Category.assoc]

theorem cap_g_twisted (SD : CapSystem D) (u : C ⟶ D) {W : Rep.{0} ℚ Γ} {a : ℕ} (b : D.X a ⟶ W)
    (hb : D.d (a+1) a ≫ b = 0) (q : ℕ) :
    (u.f (a+(q+1)) ≫ SD.cap b hb (q+1)) ≫ (W ◁ D.d (q+1) q) =
      ((-1 : ℤ)^a) • (C.d (a+q+1) (a+q) ≫ (u.f (a+q) ≫ SD.cap b hb q)) := by
  rw [Category.assoc, SD.intertwine', Preadditive.comp_zsmul, ← Category.assoc, ← Category.assoc,
    ← u.comm (a+q+1) (a+q)]
  rw [Category.assoc, Category.assoc]
  rfl

theorem CapSystem.counit' (S : CapSystem C) {W : Rep.{0} ℚ Γ} {a : ℕ} (b : C.X a ⟶ W)
    (hb : C.d (a+1) a ≫ b = 0) : S.cap b hb 0 ≫ (W ◁ S.eps) = b ≫ (ρ_ W).inv := by
  calc S.cap b hb 0 ≫ (W ◁ S.eps) = (S.cap b hb 0 ≫ (W ◁ S.eps) ≫ (ρ_ W).hom) ≫ (ρ_ W).inv := by
        simp
    _ = b ≫ (ρ_ W).inv := by rw [S.counit]

theorem cap_aug (SC : CapSystem C) (SD : CapSystem D) (u : C ⟶ D) (hueps : u.f 0 ≫ SD.eps = SC.eps)
    {W : Rep.{0} ℚ Γ} {a : ℕ} (b : D.X a ⟶ W) (hb : D.d (a+1) a ≫ b = 0) :
    (SC.cap (u.f a ≫ b) (chainMap_cocycle u b hb) 0 ≫ (W ◁ u.f 0)) ≫ (W ◁ SD.eps) =
      (u.f (a+0) ≫ SD.cap b hb 0) ≫ (W ◁ SD.eps) := by
  rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hueps, SC.counit', Category.assoc, Category.assoc, SD.counit']
  rfl

theorem carried_f {B : CellBasis C} (SC : CapSystem C) (𝒦 : CarrierData B D) (h1 : CapCellCarried SC 𝒦)
    (u : C ⟶ D) (hu : ∀ n, 𝒦.Carried (u.f n)) {W : Rep.{0} ℚ Γ} {a : ℕ} (b : D.X a ⟶ W)
    (hb : D.d (a+1) a ≫ b = 0) (q : ℕ) :
    (𝒦.tensor W).Carried (SC.cap (u.f a ≫ b) (chainMap_cocycle u b hb) q ≫ (W ◁ u.f q)) := by
  intro s
  have hmem := h1 (u.f a ≫ b) (chainMap_cocycle u b hb) q s
  have hle : Submodule.span ℚ {x | ∃ (w : W) (t : B.S q), (∀ m, 𝒦.K q t m ≤ 𝒦.K (a+q) s m) ∧
        x = (w ⊗ₜ[ℚ] B.cell q t : (W ⊗ C.X q : Rep.{0} ℚ Γ))} ≤
      (tensorK W (𝒦.K (a+q) s q)).comap (W ◁ u.f q).hom.toLinearMap := by
    rw [Submodule.span_le]
    rintro x ⟨w, t, ht, rfl⟩
    change (W ◁ u.f q).hom (w ⊗ₜ[ℚ] B.cell q t) ∈ tensorK W (𝒦.K (a+q) s q)
    rw [whiskerLeft_hom_apply]
    exact tmul_mem_tensorK W w (ht q (hu q t))
  exact hle hmem

theorem carried_g {B : CellBasis C} (SD : CapSystem D) (𝒦 : CarrierData B D) (h2 : CapCarrierPreserved SD 𝒦)
    (u : C ⟶ D) (hu : ∀ n, 𝒦.Carried (u.f n)) {W : Rep.{0} ℚ Γ} {a : ℕ} (b : D.X a ⟶ W)
    (hb : D.d (a+1) a ≫ b = 0) (q : ℕ) :
    (𝒦.tensor W).Carried (u.f (a+q) ≫ SD.cap b hb q) := by
  intro s
  exact h2 b hb q (a+q) s _ (hu (a+q) s)

/-- **Cap compatibility of a carried chain map.**  There is a homotopy (carried by the tensor carriers) between
`cap_C (u ≫ b) ≫ (W ◁ u)` and `u ≫ cap_D b`. -/
theorem cap_compat {B : CellBasis C} (SC : CapSystem C) (SD : CapSystem D) (𝒦 : CarrierData B D)
    (hsub : 𝒦.IsSubcomplex) (hac : 𝒦.Acyclic SD.eps) (h1 : CapCellCarried SC 𝒦)
    (h2 : CapCarrierPreserved SD 𝒦) (u : C ⟶ D) (hu : ∀ n, 𝒦.Carried (u.f n))
    (hueps : u.f 0 ≫ SD.eps = SC.eps) {W : Rep.{0} ℚ Γ} {a : ℕ} (b : D.X a ⟶ W)
    (hb : D.d (a+1) a ≫ b = 0) :
    ∃ h : ∀ q, C.X (a+q) ⟶ W ⊗ D.X (q+1),
      (SC.cap (u.f a ≫ b) (chainMap_cocycle u b hb) 0 ≫ (W ◁ u.f 0) - u.f (a+0) ≫ SD.cap b hb 0 =
        h 0 ≫ (W ◁ D.d 1 0)) ∧
      ∀ q, SC.cap (u.f a ≫ b) (chainMap_cocycle u b hb) (q+1) ≫ (W ◁ u.f (q+1)) -
          u.f (a+(q+1)) ≫ SD.cap b hb (q+1) =
        h (q+1) ≫ (W ◁ D.d (q+1+1) (q+1)) + ((-1 : ℤ)^a) • (C.d (a+q+1) (a+q) ≫ h q) := by
  obtain ⟨h, -, h0, hq⟩ := (𝒦.tensor W).exists_carried_homotopy (hac.tensor hsub W) a ((-1 : ℤ)^a)
    (fun q => SC.cap (u.f a ≫ b) (chainMap_cocycle u b hb) q ≫ (W ◁ u.f q))
    (fun q => u.f (a+q) ≫ SD.cap b hb q)
    (cap_f_twisted SC u b hb) (cap_g_twisted SD u b hb)
    (carried_f SC 𝒦 h1 u hu b hb) (carried_g SD 𝒦 h2 u hu b hb)
    (cap_aug SC SD u hueps b hb)
  exact ⟨h, h0, hq⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
