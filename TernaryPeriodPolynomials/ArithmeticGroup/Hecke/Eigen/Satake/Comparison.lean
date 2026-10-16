module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Coset
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Norms

@[expose] public section


/-!
# The Satake comparison of the plane and line eigenvalues

For an away-from-three correspondence `t`, the plane eigenvalue `∑ᵣ Φ_P(Levi_P r)` equals the
line eigenvalue `∑ᵣ Φ_L(Levi_L r)`. Grouping the representatives by Levi classes, the number of
representatives in the plane class of `m = (B, s)` is `|det(s⁻¹B)|` times the number `N(m)` of
radical classes modulo `ℤ²`, while (through `τ(x) = w xᵀ w⁻¹`) the number in the line class
of `(A, d)` is `N(Aᵀ, d) = N(A, d)`. The weights satisfy `Φ_L(A, d) = Φ_P(A, d) · |det(d⁻¹A)|`
by the product formula, so the two sums agree term by term.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-- Levi data `(B, s)`. -/
abbrev MP := GeneralLinearGroup (Fin 2) ℚ × ℚˣ

/-- The class subgroup `GL₂(ℤ) × 1`. -/
def ΓM0 : Subgroup MP := Γ2.prod ⊥

theorem ΓM0_le : ΓM0 ≤ Γ2.prod signs := Subgroup.prod_mono le_rfl bot_le

theorem pos_class (m m' : MP) (hm : 0 < (m.2 : ℚ)) (hm' : 0 < (m'.2 : ℚ))
    (h : m⁻¹ * m' ∈ Γ2.prod signs) : m⁻¹ * m' ∈ ΓM0 := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp h
  refine Subgroup.mem_prod.mpr ⟨h1, ?_⟩
  rw [Subgroup.mem_bot]
  rcases mem_signs.mp h2 with h | h
  · exact h
  · exfalso
    have hv := congrArg (fun u : ℚˣ => (u : ℚ)) h
    simp only [Prod.snd_mul, Prod.snd_inv, Units.val_mul, Units.val_neg, Units.val_one] at hv
    rw [Units.val_inv_eq_inv_val] at hv
    have : 0 < (m.2 : ℚ)⁻¹ * m'.2 := mul_pos (inv_pos.mpr hm) hm'
    linarith

theorem GL2_det_ne (B : GeneralLinearGroup (Fin 2) ℚ) : B.val.det ≠ 0 :=
  (GeneralLinearGroup.det B).ne_zero

/-! ### Finiteness of the lattice index -/

theorem lat_relIndex_ne_zero (A : Matrix (Fin 2) (Fin 2) ℚ) (hA : A.det ≠ 0) :
    (lat A ⊓ zLat).relIndex (lat A) ≠ 0 := by
  obtain ⟨N, hN, M, hM⟩ := RepresentationTheory.IntegerCartan.exists_clear_denominators A
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hMdet : M.det ≠ 0 := by
    intro h0
    have : (M.map (Int.cast : ℤ → ℚ)).det = 0 := by
      rw [show (Int.cast : ℤ → ℚ) = ⇑(Int.castRingHom ℚ) from rfl, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, h0, map_zero]
    rw [hM, Matrix.det_smul] at this
    exact hA ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hNq))
  obtain ⟨U, V, U', V', a, hUU', hU'U, hVV', hV'V, hMeq⟩ :=
    HeckeCommutativity.exists_eq_mul_diagonal_mul M hMdet
  set Uq := U.map (Int.cast : ℤ → ℚ)
  set Vq := V.map (Int.cast : ℤ → ℚ)
  set D : Matrix (Fin 2) (Fin 2) ℚ := diagonal ![(a 0 : ℚ) / N, (a 1 : ℚ) / N]
  have hAeq : A = Uq * D * Vq := by
    have h1 : M.map (Int.cast : ℤ → ℚ) = Uq * (diagonal fun i => (a i : ℚ)) * Vq := by
      rw [hMeq, show (Int.cast : ℤ → ℚ) = ⇑(Int.castRingHom ℚ) from rfl, Matrix.map_mul,
        Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
      rfl
    have hND : (N : ℚ) • D = diagonal fun i => (a i : ℚ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [D] <;> field_simp
    have h2 : (N : ℚ) • A = (N : ℚ) • (Uq * D * Vq) := by
      rw [← hM, h1, ← Matrix.smul_mul, ← Matrix.mul_smul, hND]
    exact smul_right_injective _ hNq h2
  have hDdet : D.det ≠ 0 := by
    intro h0
    apply hA
    rw [hAeq, Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]
  have hd0 : (a 0 : ℚ) / N ≠ 0 := by
    intro h0; apply hDdet; simp [D, det_diagonal, Fin.prod_univ_two, h0]
  have hd1 : (a 1 : ℚ) / N ≠ 0 := by
    intro h0; apply hDdet; simp [D, det_diagonal, Fin.prod_univ_two, h0]
  have hlat : lat A = (lat D).map (matHom Uq) := by
    rw [hAeq, lat_mul_int _ V V' hVV', int_mul_lat]
  have hz : zLat = zLat.map (matHom Uq) := (intMat_map_eq U U' hUU').symm
  have hinj := intMat_injective U U' hU'U
  have hinter : lat A ⊓ zLat = (lat D ⊓ zLat).map (matHom Uq) := by
    rw [AddSubgroup.map_inf_eq _ _ _ hinj, ← hlat, ← hz]
  have e1 : (lat A ⊓ zLat).relIndex (lat A) = (lat D ⊓ zLat).relIndex (lat D) := by
    rw [hinter, hlat, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  rw [e1, diag_relIndex_lat hd0 hd1]
  exact Nat.mul_ne_zero (Rat.den_nz _) (Rat.den_nz _)

/-! ### The plane count -/

theorem planeData_latt (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    planeData.latt (B, s) = lat ((s⁻¹ : ℚˣ).val • B.val) := by
  ext u
  change matHom ((s : ℚ) • (B⁻¹).val) u ∈ zLat ↔ u ∈ zLat.map (matHom ((s⁻¹ : ℚˣ).val • B.val))
  constructor
  · intro h
    exact ⟨_, h, matHom_smul_inv B s u⟩
  · rintro ⟨z, hz, rfl⟩
    rwa [matHom_inv_smul]

theorem det_smul_ne (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    ((s⁻¹ : ℚˣ).val • B.val).det ≠ 0 := by
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (GL2_det_ne B)

/-- **Lemma C**: the right-coset count is `|det(s⁻¹ B)|` times the left-coset count. -/
theorem plane_count {D : Set RationalGL3} (hDl : ∀ γ ∈ Γ, ∀ x ∈ D, γ * x ∈ D)
    (hDr : ∀ x ∈ D, ∀ γ ∈ Γ, x * γ ∈ D) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    ((((QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ planeData.latt (B, s)) ''
        planeData.S D (B, s)).ncard : ℕ) : ℚ) =
      |((s⁻¹ : ℚˣ).val • B.val).det| * (planeData.NL D (B, s) : ℚ) := by
  have hA := det_smul_ne B s
  have hlat := planeData_latt B s
  have hsat1 := planeData.S_add_latt hDr (B, s)
  rw [hlat] at hsat1 ⊢
  have c1 := card_image_mod (lat ((s⁻¹ : ℚˣ).val • B.val) ⊓ zLat) _ inf_le_left
    (planeData.S D (B, s)) hsat1
  have c2 := card_image_mod (lat ((s⁻¹ : ℚˣ).val • B.val) ⊓ zLat) zLat inf_le_right
    (planeData.S D (B, s)) (planeData.S_add_zLat hDl (B, s))
  have hi := lat_index _ hA
  have hne := lat_relIndex_ne_zero _ hA
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at c1 c2
  have key := congrArg (fun x : ℕ => (x : ℚ)) (c1.symm.trans c2)
  simp only [Nat.cast_mul] at key
  rw [← hi] at key
  have hne' : ((lat ((s⁻¹ : ℚˣ).val • B.val) ⊓ zLat).relIndex
      (lat ((s⁻¹ : ℚˣ).val • B.val)) : ℚ) ≠ 0 := by exact_mod_cast hne
  simp only [ParabolicData.NL]
  apply mul_right_cancel₀ hne'
  rw [key]
  ring

/-! ### The line count through `τ` -/

theorem line_latt_eq (A : GeneralLinearGroup (Fin 2) ℚ) (d : ℚˣ) :
    lineData.latt (A, d) = zLat.map (matHom (d.val • ((transposeGL A)⁻¹).val)) := by
  ext u
  change matHom ((d⁻¹ : ℚˣ).val • A.valᵀ) u ∈ zLat ↔ _
  have hB : A.valᵀ = (transposeGL A).val := rfl
  rw [hB]
  constructor
  · intro h
    exact ⟨_, h, matHom_inv_smul (transposeGL A) d u⟩
  · rintro ⟨z, hz, rfl⟩
    rwa [matHom_smul_inv]

theorem line_S_eq {t : HeckeCorrespondence} (ht : AwayThree t) (A : GeneralLinearGroup (Fin 2) ℚ)
    (d : ℚˣ) :
    lineData.S (DZ t.g) (A, d) =
      matHom (d.val • ((transposeGL A)⁻¹).val) '' planeData.S (DZ t.g) (transposeGL A, d) := by
  have key : ∀ v : ℚ × ℚ, τ (pU v * planeLevi (transposeGL A) d) =
      lU (matHom (d.val • ((transposeGL A)⁻¹).val) v) * lineLevi d A := by
    intro v
    rw [τ_plane, transposeGL_transposeGL]
  ext w
  constructor
  · intro hw
    refine ⟨matHom ((d⁻¹ : ℚˣ).val • (transposeGL A).val) w, ?_, matHom_inv_smul _ d w⟩
    change pU _ * planeLevi (transposeGL A) d ∈ DZ t.g
    rw [← τ_DZ_iff ht, key, matHom_inv_smul]
    exact hw
  · rintro ⟨v, hv, rfl⟩
    change lU _ * lineLevi d A ∈ DZ t.g
    rw [← key, τ_DZ_iff ht]
    exact hv

theorem line_count {t : HeckeCorrespondence} (ht : AwayThree t) (A : GeneralLinearGroup (Fin 2) ℚ)
    (d : ℚˣ) :
    ((QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ lineData.latt (A, d)) ''
        lineData.S (DZ t.g) (A, d)).ncard = planeData.NL (DZ t.g) (transposeGL A, d) := by
  let e : (ℚ × ℚ) ≃+ (ℚ × ℚ) :=
    { toFun := matHom (d.val • ((transposeGL A)⁻¹).val)
      invFun := matHom ((d⁻¹ : ℚˣ).val • (transposeGL A).val)
      left_inv := fun v => matHom_smul_inv _ d v
      right_inv := fun v => matHom_inv_smul _ d v
      map_add' := (matHom _).map_add }
  have he : zLat.map e.toAddMonoidHom = lineData.latt (A, d) := by
    rw [line_latt_eq]; rfl
  let q := QuotientAddGroup.congr zLat (lineData.latt (A, d)) e he
  have himg : (QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ lineData.latt (A, d)) ''
      lineData.S (DZ t.g) (A, d) =
      q '' ((QuotientAddGroup.mk : ℚ × ℚ → (ℚ × ℚ) ⧸ zLat) '' planeData.S (DZ t.g) (transposeGL A, d)) := by
    rw [line_S_eq ht, Set.image_image, Set.image_image]
    rfl
  rw [himg, Set.ncard_image_of_injective _ q.injective]
  rfl

/-! ### Smith invariance of the count -/

theorem NL_transpose {D : Set RationalGL3} (hDl : ∀ γ ∈ Γ, ∀ x ∈ D, γ * x ∈ D)
    (hDr : ∀ x ∈ D, ∀ γ ∈ Γ, x * γ ∈ D) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    planeData.NL D (transposeGL B, s) = planeData.NL D (B, s) := by
  obtain ⟨U, V, hU, hV, hUV⟩ := RepresentationTheory.IntegerCartan.rat_transpose_equiv B.val
    (GL2_det_ne B)
  let k₁ : GeneralLinearGroup (Fin 2) ℚ :=
    GeneralLinearGroup.map (Int.castRingHom ℚ) (Matrix.nonsingInvUnit U hU)
  let k₂ : GeneralLinearGroup (Fin 2) ℚ :=
    GeneralLinearGroup.map (Int.castRingHom ℚ) (Matrix.nonsingInvUnit V hV)
  have hk₁ : ((k₁, 1) : MP) ∈ Γ2.prod signs := ⟨⟨_, rfl⟩, one_mem _⟩
  have hk₂ : ((k₂, 1) : MP) ∈ Γ2.prod signs := ⟨⟨_, rfl⟩, one_mem _⟩
  have heq : ((transposeGL B, s) : MP) = ((k₁, 1) : MP) * (B, s) * (k₂, 1) := by
    refine Prod.ext ?_ ?_
    · apply Units.ext
      change B.valᵀ = (U.map (Int.cast : ℤ → ℚ)) * B.val * (V.map (Int.cast : ℤ → ℚ))
      rw [hUV]
    · simp
  rw [heq, planeData.NL_mul_right hDr _ hk₂, planeData.NL_mul_left hDl _ hk₁]

/-! ### Three-adic integrality -/

theorem Int3_int (z : ℤ) : Int3 (z : ℚ) := by
  unfold Int3
  rw [Rat.cast_intCast]
  exact Padic.norm_int_le_one z

theorem Int3_add {a b : ℚ} (ha : Int3 a) (hb : Int3 b) : Int3 (a + b) := by
  unfold Int3 at *
  rw [Rat.cast_add]
  exact (Padic.nonarchimedean _ _).trans (max_le ha hb)

theorem Int3_mul {a b : ℚ} (ha : Int3 a) (hb : Int3 b) : Int3 (a * b) := by
  unfold Int3 at *
  rw [Rat.cast_mul, norm_mul]
  exact (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem Int3_neg {a : ℚ} (ha : Int3 a) : Int3 (-a) := by
  unfold Int3 at *
  rwa [Rat.cast_neg, norm_neg]

theorem Int3_sub {a b : ℚ} (ha : Int3 a) (hb : Int3 b) : Int3 (a - b) := by
  rw [sub_eq_add_neg]; exact Int3_add ha (Int3_neg hb)

/-- All entries are three-adically integral. -/
def Int3Mat (x : RationalGL3) : Prop := ∀ i j, Int3 (x.val i j)

theorem Int3Mat_mul {x y : RationalGL3} (hx : Int3Mat x) (hy : Int3Mat y) : Int3Mat (x * y) := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  exact Int3_add (Int3_add (Int3_mul (hx _ _) (hy _ _)) (Int3_mul (hx _ _) (hy _ _)))
    (Int3_mul (hx _ _) (hy _ _))

theorem Int3Mat_Γ {x : RationalGL3} (hx : x ∈ Γ) : Int3Mat x := by
  obtain ⟨k, rfl⟩ := hx
  intro i j
  have : (integralRational k).val i j = ((k.val i j : ℤ) : ℚ) := rfl
  rw [this]
  exact Int3_int _

theorem DZ_int3 {t : HeckeCorrespondence} (ht : AwayThree t) {x : RationalGL3}
    (hx : x ∈ DZ t.g) : Int3Mat x ∧ Int3Mat x⁻¹ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have hg : Int3Mat t.g := by
    intro i j
    unfold Int3
    exact integralAtThree_norm (ht.1 i j).1
  have hg' : Int3Mat t.g⁻¹ := by
    intro i j
    unfold Int3
    exact integralAtThree_norm (ht.1 i j).2
  refine ⟨Int3Mat_mul (Int3Mat_mul (Int3Mat_Γ ha) hg) (Int3Mat_Γ hb), ?_⟩
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
  exact Int3Mat_mul (Int3Mat_Γ (Γ.inv_mem hb)) (Int3Mat_mul hg' (Int3Mat_Γ (Γ.inv_mem ha)))

theorem plane_int3 {t : HeckeCorrespondence} (ht : AwayThree t) {v : ℚ × ℚ}
    {A : GeneralLinearGroup (Fin 2) ℚ} {d : ℚˣ} (h : pU v * planeLevi A d ∈ DZ t.g) :
    Int3 (d : ℚ) ∧ Int3 (d : ℚ)⁻¹ ∧ Int3 A.val.det ∧ Int3 (A.val.det)⁻¹ := by
  obtain ⟨h1, h2⟩ := DZ_int3 ht h
  have hinv : (pU v * planeLevi A d)⁻¹ = planeLevi A⁻¹ d⁻¹ * pU (-v) := by
    rw [_root_.mul_inv_rev, pU_neg]
    congr 1
  rw [hinv] at h2
  have e1 : (pU v * planeLevi A d).val 2 2 = d := by
    simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have e2 : (planeLevi A⁻¹ d⁻¹ * pU (-v)).val 2 2 = (d : ℚ)⁻¹ := by
    simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three,
      Units.val_inv_eq_inv_val]
  have e3 : A.val.det = (pU v * planeLevi A d).val 0 0 * (pU v * planeLevi A d).val 1 1 -
      (pU v * planeLevi A d).val 0 1 * (pU v * planeLevi A d).val 1 0 := by
    rw [Matrix.det_fin_two]
    simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have e4 : (A.val.det)⁻¹ = (planeLevi A⁻¹ d⁻¹ * pU (-v)).val 0 0 * (planeLevi A⁻¹ d⁻¹ * pU (-v)).val 1 1 -
      (planeLevi A⁻¹ d⁻¹ * pU (-v)).val 0 1 * (planeLevi A⁻¹ d⁻¹ * pU (-v)).val 1 0 := by
    have : (A.val.det)⁻¹ = (A⁻¹).val.det := by
      have := congrArg Units.val (map_inv GeneralLinearGroup.det A)
      rw [Units.val_inv_eq_inv_val] at this
      exact this.symm
    rw [this, Matrix.det_fin_two]
    simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨e1 ▸ h1 2 2, e2 ▸ h2 2 2, ?_, ?_⟩
  · rw [e3]
    exact Int3_sub (Int3_mul (h1 _ _) (h1 _ _)) (Int3_mul (h1 _ _) (h1 _ _))
  · rw [e4]
    exact Int3_sub (Int3_mul (h2 _ _) (h2 _ _)) (Int3_mul (h2 _ _) (h2 _ _))

end TernaryPeriodPolynomials.HeckeEigen.Satake
