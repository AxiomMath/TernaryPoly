module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Cells

@[expose] public section


/-!
# Equivariant acyclic carriers: chain maps and homotopies

Let `C` be a chain complex of representations with a free `Γ`-cell basis `B` and `D` another one.  A `CarrierData`
assigns to every cell `s` subspaces `K s m ⊆ D.X m` (`Γ`-equivariantly in `s`) so that the boundary of `s` is a
combination of cells with smaller carriers.  If the carriers are acyclic (`CarrierAcyclic`: cycles of `K s` are
boundaries in `K s`, relative to an augmentation `aug`), then

* `exists_carried_chainMap`: there is a chain map `C ⟶ D` carried by `K` and compatible with the augmentations;
* `exists_carried_homotopy`: two carried "twisted chain maps" `C.X (a+q) ⟶ D.X q` with the same augmentation are
  homotopic by a carried homotopy.

The proofs are the standard induction over the degree, each step an application of `exists_equivariant_lift`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

/-- Carriers: a family of subspaces of `D` attached to every cell of `C`. -/
structure CarrierData {C : ChainComplex (Rep.{0} ℚ Γ) ℕ} (B : CellBasis C)
    (D : ChainComplex (Rep.{0} ℚ Γ) ℕ) where
  K : ∀ n, B.S n → ∀ m, Submodule ℚ (D.X m)
  K_smul : ∀ n (γ : Γ) (s : B.S n) m, K n (γ • s) m = (K n s m).map ((D.X m).ρ γ)
  K_face : ∀ n (s : B.S (n+1)), (C.d (n+1) n).hom (B.cell (n+1) s) ∈
    Submodule.span ℚ {x | ∃ t : B.S n, (∀ m, K n t m ≤ K (n+1) s m) ∧ x = B.cell n t}

variable {C : ChainComplex (Rep.{0} ℚ Γ) ℕ} {B : CellBasis C} {D : ChainComplex (Rep.{0} ℚ Γ) ℕ}

/-- A morphism `C.X n ⟶ D.X m` is carried if it sends each cell into its carrier. -/
def CarrierData.Carried (𝒦 : CarrierData B D) {n m : ℕ} (g : C.X n ⟶ D.X m) : Prop :=
  ∀ s : B.S n, g.hom (B.cell n s) ∈ 𝒦.K n s m

/-- A carried morphism sends the boundary of a cell into the carrier of that cell. -/
theorem CarrierData.Carried.face {𝒦 : CarrierData B D} {n m : ℕ} {g : C.X n ⟶ D.X m}
    (hg : 𝒦.Carried g) (s : B.S (n+1)) :
    g.hom ((C.d (n+1) n).hom (B.cell (n+1) s)) ∈ 𝒦.K (n+1) s m := by
  have h := 𝒦.K_face n s
  have hle : Submodule.span ℚ {x | ∃ t : B.S n, (∀ m, 𝒦.K n t m ≤ 𝒦.K (n+1) s m) ∧ x = B.cell n t} ≤
      (𝒦.K (n+1) s m).comap g.hom.toLinearMap := by
    rw [Submodule.span_le]
    rintro x ⟨t, ht, rfl⟩
    exact ht m (hg t)
  exact hle h

theorem CarrierData.Carried.zero {𝒦 : CarrierData B D} {n m : ℕ} : 𝒦.Carried (0 : C.X n ⟶ D.X m) := by
  intro s
  exact Submodule.zero_mem _

theorem CarrierData.Carried.sub {𝒦 : CarrierData B D} {n m : ℕ} {g g' : C.X n ⟶ D.X m}
    (hg : 𝒦.Carried g) (hg' : 𝒦.Carried g') : 𝒦.Carried (g - g') := by
  intro s
  exact Submodule.sub_mem _ (hg s) (hg' s)

/-- Acyclicity of the carriers relative to an augmentation `aug : D.X 0 ⟶ A`. -/
structure CarrierData.Acyclic (𝒦 : CarrierData B D) {A : Rep.{0} ℚ Γ} (aug : D.X 0 ⟶ A) : Prop where
  aug_d : D.d 1 0 ≫ aug = 0
  acyc0 : ∀ n (s : B.S n) (y : D.X 0), y ∈ 𝒦.K n s 0 → aug.hom y = 0 →
    ∃ x ∈ 𝒦.K n s 1, (D.d 1 0).hom x = y
  acyc : ∀ n (s : B.S n) m (y : D.X (m+1)), y ∈ 𝒦.K n s (m+1) → (D.d (m+1) m).hom y = 0 →
    ∃ x ∈ 𝒦.K n s (m+2), (D.d (m+2) (m+1)).hom x = y

/-- Carried morphisms with prescribed image under a morphism `φ`: the abstract lifting step. -/
theorem CellBasis.exists_lift (B : CellBasis C) {n : ℕ} {Y Z : Rep.{0} ℚ Γ}
    (KY : B.S n → Submodule ℚ Y) (hKY : ∀ (γ : Γ) (s : B.S n), KY (γ • s) = (KY s).map (Y.ρ γ))
    (φ : Y ⟶ Z) (Φ : C.X n ⟶ Z)
    (h : ∀ s, Φ.hom (B.cell n s) ∈ (KY s).map φ.hom.toLinearMap) :
    ∃ Ψ : C.X n ⟶ Y, (∀ s, Ψ.hom (B.cell n s) ∈ KY s) ∧ Ψ ≫ φ = Φ := by
  obtain ⟨y, hy, hyK, hyφ⟩ := exists_equivariant_lift (B.free n) φ KY hKY
    (fun s => Φ.hom (B.cell n s))
    (fun γ s => by rw [B.cell_smul]; exact Rep.hom_comm_apply Φ γ _) h
  refine ⟨B.lift n y hy, fun s => ?_, ?_⟩
  · rw [B.lift_cell n y hy s]; exact hyK s
  · apply B.hom_ext n
    intro s
    change φ.hom ((B.lift n y hy).hom (B.cell n s)) = Φ.hom (B.cell n s)
    rw [B.lift_cell n y hy s]
    exact hyφ s

/-- The primitive step in positive degrees. -/
theorem CarrierData.exists_carried_primitive (𝒦 : CarrierData B D) {A : Rep.{0} ℚ Γ} {aug : D.X 0 ⟶ A}
    (hac : 𝒦.Acyclic aug) {n : ℕ} (m : ℕ) (Φ : C.X n ⟶ D.X (m+1)) (hΦ : 𝒦.Carried Φ)
    (hcyc : Φ ≫ D.d (m+1) m = 0) :
    ∃ Ψ : C.X n ⟶ D.X (m+2), 𝒦.Carried Ψ ∧ Ψ ≫ D.d (m+2) (m+1) = Φ := by
  obtain ⟨Ψ, hΨK, hΨ⟩ := B.exists_lift (fun s => 𝒦.K n s (m+2)) (fun γ s => 𝒦.K_smul n γ s (m+2))
    (D.d (m+2) (m+1)) Φ (fun s => by
      obtain ⟨x, hx, hxd⟩ := hac.acyc n s m (Φ.hom (B.cell n s)) (hΦ s) (by
        have := congrArg (fun ψ : C.X n ⟶ D.X m => ψ.hom (B.cell n s)) hcyc
        simpa using this)
      exact ⟨x, hx, hxd⟩)
  exact ⟨Ψ, hΨK, hΨ⟩

/-- The primitive step in degree zero. -/
theorem CarrierData.exists_carried_primitive0 (𝒦 : CarrierData B D) {A : Rep.{0} ℚ Γ} {aug : D.X 0 ⟶ A}
    (hac : 𝒦.Acyclic aug) {n : ℕ} (Φ : C.X n ⟶ D.X 0) (hΦ : 𝒦.Carried Φ) (hcyc : Φ ≫ aug = 0) :
    ∃ Ψ : C.X n ⟶ D.X 1, 𝒦.Carried Ψ ∧ Ψ ≫ D.d 1 0 = Φ := by
  obtain ⟨Ψ, hΨK, hΨ⟩ := B.exists_lift (fun s => 𝒦.K n s 1) (fun γ s => 𝒦.K_smul n γ s 1)
    (D.d 1 0) Φ (fun s => by
      obtain ⟨x, hx, hxd⟩ := hac.acyc0 n s (Φ.hom (B.cell n s)) (hΦ s) (by
        have := congrArg (fun ψ : C.X n ⟶ A => ψ.hom (B.cell n s)) hcyc
        simpa using this)
      exact ⟨x, hx, hxd⟩)
  exact ⟨Ψ, hΨK, hΨ⟩

theorem CarrierData.Carried.comp_left {𝒦 : CarrierData B D} {n m : ℕ} {g : C.X n ⟶ D.X m}
    (hg : 𝒦.Carried g) (ε : ℤ) : 𝒦.Carried (ε • g) := by
  intro s
  have : (ε • g).hom (B.cell n s) = ε • g.hom (B.cell n s) := rfl
  rw [this]
  exact Submodule.smul_of_tower_mem _ ε (hg s)

theorem CarrierData.Carried.add {𝒦 : CarrierData B D} {n m : ℕ} {g g' : C.X n ⟶ D.X m}
    (hg : 𝒦.Carried g) (hg' : 𝒦.Carried g') : 𝒦.Carried (g + g') := by
  intro s
  exact Submodule.add_mem _ (hg s) (hg' s)

/-- A carried morphism precomposed with the boundary of the complex `C` is carried (shifted by a degree). -/
theorem CarrierData.Carried.d_comp {𝒦 : CarrierData B D} {n m : ℕ} {g : C.X n ⟶ D.X m}
    (hg : 𝒦.Carried g) : 𝒦.Carried (C.d (n+1) n ≫ g) := by
  intro s
  exact hg.face s

/-- **Carried homotopies.**  Two carried twisted chain maps `C.X (a+q) ⟶ D.X q` with the same augmentation are
homotopic by a carried homotopy. -/
theorem CarrierData.exists_carried_homotopy (𝒦 : CarrierData B D) {A : Rep.{0} ℚ Γ} {aug : D.X 0 ⟶ A}
    (hac : 𝒦.Acyclic aug) (a : ℕ) (ε : ℤ) (f g : ∀ q, C.X (a+q) ⟶ D.X q)
    (hf : ∀ q, f (q+1) ≫ D.d (q+1) q = ε • (C.d (a+q+1) (a+q) ≫ f q))
    (hg : ∀ q, g (q+1) ≫ D.d (q+1) q = ε • (C.d (a+q+1) (a+q) ≫ g q))
    (hfc : ∀ q, 𝒦.Carried (f q)) (hgc : ∀ q, 𝒦.Carried (g q))
    (haug : f 0 ≫ aug = g 0 ≫ aug) :
    ∃ h : ∀ q, C.X (a+q) ⟶ D.X (q+1), (∀ q, 𝒦.Carried (h q)) ∧ f 0 - g 0 = h 0 ≫ D.d 1 0 ∧
      ∀ q, f (q+1) - g (q+1) = h (q+1) ≫ D.d (q+1+1) (q+1) + ε • (C.d (a+q+1) (a+q) ≫ h q) := by
  let State : ℕ → Type := fun q =>
    {h : C.X (a+q) ⟶ D.X (q+1) // 𝒦.Carried h ∧
      C.d (a+q+1) (a+q) ≫ (f q - g q - h ≫ D.d (q+1) q) = 0}
  obtain ⟨seq, hseq0, hseq⟩ := exists_sequence State
    (fun s => f 0 - g 0 = s.1 ≫ D.d 1 0)
    (fun q s s' => s'.1 ≫ D.d (q+1+1) (q+1) = f (q+1) - g (q+1) - ε • (C.d (a+q+1) (a+q) ≫ s.1))
    (by
      obtain ⟨Ψ, hΨc, hΨ⟩ := 𝒦.exists_carried_primitive0 hac (f 0 - g 0) ((hfc 0).sub (hgc 0))
        (by rw [Preadditive.sub_comp, haug, sub_self])
      refine ⟨⟨Ψ, hΨc, ?_⟩, hΨ.symm⟩
      rw [hΨ, sub_self, comp_zero])
    (by
      rintro q ⟨h, hc, hcyc⟩
      have hΦc : 𝒦.Carried (f (q+1) - g (q+1) - ε • (C.d (a+q+1) (a+q) ≫ h)) :=
        ((hfc (q+1)).sub (hgc (q+1))).sub (hc.d_comp.comp_left ε)
      have hΦcyc : (f (q+1) - g (q+1) - ε • (C.d (a+q+1) (a+q) ≫ h)) ≫ D.d (q+1) q = 0 := by
        have h1 : (f (q+1) - g (q+1) - ε • (C.d (a+q+1) (a+q) ≫ h)) ≫ D.d (q+1) q =
            ε • (C.d (a+q+1) (a+q) ≫ (f q - g q - h ≫ D.d (q+1) q)) := by
          simp only [Preadditive.sub_comp, Preadditive.zsmul_comp, Category.assoc, hf, hg,
            Preadditive.comp_sub, smul_sub]
        rw [h1, hcyc, smul_zero]
      obtain ⟨Ψ, hΨc, hΨ⟩ := 𝒦.exists_carried_primitive hac q _ hΦc hΦcyc
      refine ⟨⟨Ψ, hΨc, ?_⟩, hΨ⟩
      have h2 : f (q+1) - g (q+1) - Ψ ≫ D.d (q+1+1) (q+1) = ε • (C.d (a+q+1) (a+q) ≫ h) := by
        rw [hΨ]; abel
      rw [h2]
      have hdd : C.d (a+(q+1)+1) (a+(q+1)) ≫ C.d (a+q+1) (a+q) = 0 := C.d_comp_d _ _ _
      rw [Preadditive.comp_zsmul, ← Category.assoc, hdd, zero_comp, smul_zero])
  refine ⟨fun q => (seq q).1, fun q => (seq q).2.1, hseq0, fun q => ?_⟩
  have := hseq q
  rw [this]
  abel

/-- The "cycle" condition for the degree-`m` component of a chain map under construction. -/
def CarrierData.CycCond (_𝒦 : CarrierData B D) {A : Rep.{0} ℚ Γ} (aug : D.X 0 ⟶ A) :
    ∀ m, (C.X m ⟶ D.X m) → Prop
  | 0, g => C.d 1 0 ≫ g ≫ aug = 0
  | m+1, g => C.d (m+2) (m+1) ≫ g ≫ D.d (m+1) m = 0

/-- **Carried chain maps.**  There is a chain map `C ⟶ D` carried by `K` with prescribed augmentation. -/
theorem CarrierData.exists_carried_chainMap (𝒦 : CarrierData B D) {A : Rep.{0} ℚ Γ} {aug : D.X 0 ⟶ A}
    (hac : 𝒦.Acyclic aug) (augC : C.X 0 ⟶ A) (haugC : C.d 1 0 ≫ augC = 0)
    (hsurj : ∀ s : B.S 0, augC.hom (B.cell 0 s) ∈ (𝒦.K 0 s 0).map aug.hom.toLinearMap) :
    ∃ u : C ⟶ D, (∀ n, 𝒦.Carried (u.f n)) ∧ u.f 0 ≫ aug = augC := by
  let State : ℕ → Type := fun m => {g : C.X m ⟶ D.X m // 𝒦.Carried g ∧ 𝒦.CycCond aug m g}
  obtain ⟨seq, hseq0, hseq⟩ := exists_sequence State
    (fun s => s.1 ≫ aug = augC)
    (fun m s s' => s'.1 ≫ D.d (m+1) m = C.d (m+1) m ≫ s.1)
    (by
      obtain ⟨g0, hg0c, hg0⟩ := B.exists_lift (fun s => 𝒦.K 0 s 0) (fun γ s => 𝒦.K_smul 0 γ s 0)
        aug augC hsurj
      refine ⟨⟨g0, hg0c, ?_⟩, hg0⟩
      change C.d 1 0 ≫ g0 ≫ aug = 0
      rw [hg0, haugC])
    (by
      rintro m ⟨g, hgc, hgcyc⟩
      cases m with
      | zero =>
        obtain ⟨Ψ, hΨc, hΨ⟩ := 𝒦.exists_carried_primitive0 hac (C.d 1 0 ≫ g) hgc.d_comp
          (by rw [Category.assoc]; exact hgcyc)
        refine ⟨⟨Ψ, hΨc, ?_⟩, hΨ⟩
        change C.d 2 1 ≫ Ψ ≫ D.d 1 0 = 0
        rw [hΨ, ← Category.assoc, C.d_comp_d, zero_comp]
      | succ m =>
        obtain ⟨Ψ, hΨc, hΨ⟩ := 𝒦.exists_carried_primitive hac m (C.d (m+2) (m+1) ≫ g) hgc.d_comp
          (by rw [Category.assoc]; exact hgcyc)
        refine ⟨⟨Ψ, hΨc, ?_⟩, hΨ⟩
        change C.d (m+1+2) (m+1+1) ≫ Ψ ≫ D.d (m+1+1) (m+1) = 0
        rw [hΨ, ← Category.assoc, C.d_comp_d, zero_comp])
  refine ⟨{ f := fun m => (seq m).1, comm' := ?_ }, fun n => (seq n).2.1, hseq0⟩
  intro i j hij
  obtain rfl : i = j + 1 := hij.symm
  exact hseq j

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
