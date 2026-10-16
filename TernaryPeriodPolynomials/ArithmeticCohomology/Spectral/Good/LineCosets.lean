module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LineCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.AmbientHecke

@[expose] public section


/-!
# The local `T_p` correspondence at the good line

For a prime `p ≠ 3`, the local cosets of `Γ diag(p,1,1) Γ` at the good line `⟨e₃⟩`, whose
stabilizer is `Λ₁ = {Q(3b, m, 1)}`, are represented by the `p + 1` Levi elements
`ℓ_j = diag(B_j, 1)` (`B_j a_j = p`) and the `p²` radical elements `τ_c = Q(3c, 1, εp)`
(`c ∈ (ℤ/p)²`, `εp = ±p ≡ 1 mod 3`). This file builds the local correspondence
`goodLineCosets p` and computes its transitions.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.GoodLineCosets

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets LineCoordinates AmbientHecke

variable (p : Nat.Primes)

/-! ### The sign of `εp` and residues modulo `p` -/

/-- The sign `εp / p`. -/
def sgnL : ℤ := if (p.val : ℤ) % 3 = 1 then 1 else -1

theorem epsP_eq : epsP p = sgnL p * p.val := by
  unfold sgnL epsP
  split_ifs <;> ring

theorem sgnL_sq : sgnL p * sgnL p = 1 := by
  unfold sgnL
  split_ifs <;> norm_num

theorem p_pos : (0 : ℤ) < p.val := by exact_mod_cast p.property.pos

/-- The residue of `z` modulo `p`. -/
def res1 (z : ℤ) : Fin p.val :=
  ⟨(z % (p.val : ℤ)).toNat, by
    have h1 := Int.emod_nonneg z (p_pos p).ne'
    have h2 := Int.emod_lt_of_pos z (p_pos p)
    omega⟩

/-- The residue vector. -/
def crep (x : ℤ × ℤ) : Fin p.val × Fin p.val := (res1 p x.1, res1 p x.2)

/-- The integral representative of a residue vector. -/
def cvec (c : Fin p.val × Fin p.val) : ℤ × ℤ := ((c.1.val : ℤ), (c.2.val : ℤ))

/-- The quotient vector: `x = cvec (crep x) + εp • cq x`. -/
def cq (x : ℤ × ℤ) : ℤ × ℤ := (sgnL p * (x.1 / p.val), sgnL p * (x.2 / p.val))

theorem res1_val (z : ℤ) : ((res1 p z).val : ℤ) = z % (p.val : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (p_pos p).ne')

theorem crep_spec (x : ℤ × ℤ) : x = cvec p (crep p x) + epsP p • cq p x := by
  have h1 := Int.emod_add_mul_ediv x.1 (p.val : ℤ)
  have h2 := Int.emod_add_mul_ediv x.2 (p.val : ℤ)
  have hs := sgnL_sq p
  ext
  · simp only [cvec, crep, cq, Prod.fst_add, Prod.smul_fst, smul_eq_mul, res1_val, epsP_eq]
    linear_combination -h1 - (p.val * (x.1 / p.val)) * hs
  · simp only [cvec, crep, cq, Prod.snd_add, Prod.smul_snd, smul_eq_mul, res1_val, epsP_eq]
    linear_combination -h2 - (p.val * (x.2 / p.val)) * hs

theorem res1_unique (a b : Fin p.val) (z : ℤ) (h : (a.val : ℤ) - b.val = p.val * z) : a = b := by
  have ha := a.isLt
  have hb := b.isLt
  have hzero := Int.eq_zero_of_abs_lt_dvd (⟨z, h⟩ : (p.val : ℤ) ∣ (a.val : ℤ) - b.val)
    (by rw [abs_lt]; constructor <;> omega)
  apply Fin.ext
  omega

theorem crep_unique (c c' : Fin p.val × Fin p.val) (z : ℤ × ℤ)
    (h : cvec p c - cvec p c' = epsP p • z) : c = c' := by
  rw [epsP_eq] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [cvec, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  ext
  · exact congrArg Fin.val (res1_unique p c.1 c'.1 (sgnL p * z.1) (by rw [h1]; ring))
  · exact congrArg Fin.val (res1_unique p c.2 c'.2 (sgnL p * z.2) (by rw [h2]; ring))

theorem crep_cvec_add (c : Fin p.val × Fin p.val) (z : ℤ × ℤ) :
    crep p (cvec p c + epsP p • z) = c := by
  symm
  apply crep_unique p c _ (cq p (cvec p c + epsP p • z) - z)
  have h := crep_spec p (cvec p c + epsP p • z)
  rw [smul_sub]
  calc cvec p c - cvec p (crep p (cvec p c + epsP p • z))
      = (cvec p c + epsP p • z) - cvec p (crep p (cvec p c + epsP p • z)) - epsP p • z := by abel
    _ = _ := by rw [← sub_eq_iff_eq_add'.mpr h]

/-! ### The integral matrices `B_j` -/

/-- `B_j` as an integral matrix. -/
def Bint : Option (Fin p.val) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![1, 0; 0, (p.val : ℤ)]
  | some i => !![(p.val : ℤ), -(i.val : ℤ); 0, 1]

theorem Bmat_eq (j : Option (Fin p.val)) : Bmat p j = (Bint p j).map (Int.castRingHom ℚ) := by
  cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [Bmat, Bint]

theorem vmul_BGL (b : ℤ × ℤ) (j : Option (Fin p.val)) :
    vmul (icast b) (BGL p j).val = icast (ivmul b (Bint p j)) := by
  rw [BGL_val, Bmat_eq, vmul_icast]

/-! ### The representatives -/

/-- The index type: Levi-type `inl j`, radical-type `inr c`. -/
abbrev LIdx := Option (Fin p.val) ⊕ (Fin p.val × Fin p.val)

/-- `ℓ_j = Q(0, B_j, 1)` and `τ_c = Q(3c, 1, εp)`. -/
def rExpl : LIdx p → RationalGL3
  | .inl j => Q 0 (BGL p j) 1
  | .inr c => Q ((3 : ℚ) • icast (cvec p c)) 1 (epsU p)

theorem icast_smul_three (b : ℤ × ℤ) : (3 : ℚ) • icast b = icast ((3 : ℤ) • b) := by
  simp [icast]

theorem rExpl_injective : Function.Injective (rExpl p) := by
  intro i i' h
  rcases i with j | c <;> rcases i' with j' | c' <;> simp only [rExpl] at h
  · obtain ⟨-, hB, -⟩ := Q_injective h
    rw [BGL_injective p hB]
  · obtain ⟨-, -, hd⟩ := Q_injective h
    exact absurd hd.symm (epsU_ne_one p)
  · obtain ⟨-, -, hd⟩ := Q_injective h
    exact absurd hd (epsU_ne_one p)
  · obtain ⟨hc, -, -⟩ := Q_injective h
    rw [icast_smul_three, icast_smul_three] at hc
    have := icast_injective hc
    have h3 : cvec p c = cvec p c' := by
      have := congrArg (fun x : ℤ × ℤ => x) this
      ext
      · have e := congrArg Prod.fst this
        simp at e
        exact e
      · have e := congrArg Prod.snd this
        simp at e
        exact e
    rw [crep_unique p c c' 0 (by rw [h3, sub_self, smul_zero])]

/-! ### Products with elements of `Λ₁` -/

theorem levi_product (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    (rExpl p (.inl j))⁻¹ * Qint b m * rExpl p (.inl (arithmeticNext p m j)) =
      Qint (ivmul b (Bint p j)) (arithmeticDelta p m j) := by
  simp only [rExpl, Qint]
  rw [Q_inv, Q_mul, Q_mul]
  congr 1
  · rw [inv_inv, vmul_smul, vmul_BGL, vmul_zero, vmul_zero]
    simp [icast_smul_three]
  · rw [mul_assoc]
    exact trans_levi p m j
  · simp

theorem radical_vec (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) :
    -(((epsU p)⁻¹ : ℚˣ) : ℚ) • vmul ((3 : ℚ) • icast (cvec p c)) (1 : GL (Fin 2) ℚ).val +
        (((epsU p)⁻¹ : ℚˣ) : ℚ) • vmul ((3 : ℚ) • icast b) ((1 : GL (Fin 2) ℚ)⁻¹ : GL (Fin 2) ℚ).val +
      ((((epsU p)⁻¹ * 1 : ℚˣ)) : ℚ) •
        vmul ((3 : ℚ) • icast (cvec p (crep p (ivmul (cvec p c - b) m.val))))
          ((1⁻¹ * integralEmbed m)⁻¹ : GL (Fin 2) ℚ).val =
      (3 : ℚ) • icast (-ivmul (cq p (ivmul (cvec p c - b) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val) := by
  set x := ivmul (cvec p c - b) m.val
  have hx := crep_spec p x
  have hc : icast (cvec p (crep p x)) = icast x - (epsP p : ℚ) • icast (cq p x) := by
    rw [icast_smul_int, ← icast_sub]
    exact congrArg icast (eq_sub_of_add_eq hx.symm)
  have hxm : vmul (icast x) ((integralEmbed m)⁻¹ : GL (Fin 2) ℚ).val = icast (cvec p c - b) := by
    rw [← map_inv, vmul_integralEmbed, ivmul_inv_cancel]
  have he : (epsP p : ℚ) ≠ 0 := epsP_ne_zero p
  rw [inv_one, one_mul, mul_one, Units.val_one, vmul_one, vmul_one, hc, vmul_smul, vmul_sub,
    vmul_smul, hxm, ← map_inv, vmul_integralEmbed, icast_neg, icast_sub]
  simp only [Units.val_inv_eq_inv_val, epsU_val, smul_sub, smul_smul, smul_neg]
  rw [show (epsP p : ℚ)⁻¹ * (3 * (epsP p : ℚ)) = 3 by field_simp]
  module

theorem radical_product (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) :
    (rExpl p (.inr c))⁻¹ * Qint b m * rExpl p (.inr (crep p (ivmul (cvec p c - b) m.val))) =
      Qint (-ivmul (cq p (ivmul (cvec p c - b) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val) m := by
  simp only [rExpl, Qint]
  rw [Q_inv, Q_mul, Q_mul]
  congr 1
  · exact radical_vec p b m c
  · simp
  · simp

/-! ### The local correspondence -/

theorem ivmul_sub (b c : ℤ × ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ivmul (b - c) A = ivmul b A - ivmul c A := by
  simp only [ivmul, Prod.fst_sub, Prod.snd_sub]
  ext <;> simp <;> ring

theorem ivmul_add (b c : ℤ × ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ivmul (b + c) A = ivmul b A + ivmul c A := by
  simp only [ivmul, Prod.fst_add, Prod.snd_add]
  ext <;> simp <;> ring

theorem ivmul_smul (z : ℤ) (b : ℤ × ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ivmul (z • b) A = z • ivmul b A := by
  simp only [ivmul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ext <;> simp <;> ring

theorem ivmul_neg (b : ℤ × ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) : ivmul (-b) A = -ivmul b A := by
  simp only [ivmul, Prod.fst_neg, Prod.snd_neg]
  ext <;> simp <;> ring

/-- The radical index with `τ_{c'}⁻¹ g τ_c ∈ Λ₁`. -/
def prevRad (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) : Fin p.val × Fin p.val :=
  crep p (ivmul (cvec p c) (m⁻¹ : GL (Fin 2) ℤ).val + b)

theorem next_prevRad (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) :
    crep p (ivmul (cvec p (prevRad p b m c) - b) m.val) = c := by
  set y := ivmul (cvec p c) (m⁻¹ : GL (Fin 2) ℤ).val + b
  have hy := crep_spec p y
  have h : cvec p (prevRad p b m c) - b = ivmul (cvec p c) (m⁻¹ : GL (Fin 2) ℤ).val - epsP p • cq p y := by
    have : cvec p (prevRad p b m c) = y - epsP p • cq p y := eq_sub_of_add_eq hy.symm
    rw [this]
    simp only [y]
    abel
  rw [h, ivmul_sub, ivmul_cancel_inv, ivmul_smul, sub_eq_add_neg, ← smul_neg, crep_cvec_add]

theorem rExpl_stable (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (i : LIdx p) :
    ∃ i' : LIdx p, (rExpl p i')⁻¹ * (Qint b m * rExpl p i) ∈ Λ₁ := by
  rcases i with j | c
  · refine ⟨.inl (prevIdx p m j), ?_⟩
    have h := levi_product p b m (prevIdx p m j)
    rw [next_prevIdx] at h
    rw [← mul_assoc, h]
    exact Qint_mem _ _
  · refine ⟨.inr (prevRad p b m c), ?_⟩
    have h := radical_product p b m (prevRad p b m c)
    rw [next_prevRad] at h
    rw [← mul_assoc, h]
    exact Qint_mem _ _

theorem rExpl_disjoint (i i' : LIdx p) (h : (rExpl p i)⁻¹ * rExpl p i' ∈ Λ₁) : i = i' := by
  rcases i with j | c <;> rcases i' with j' | c' <;> simp only [rExpl] at h <;>
    rw [Q_inv, Q_mul, Q_mem_iff] at h
  · obtain ⟨-, -, ⟨μ, hμ⟩⟩ := h
    rw [BGL_unique p hμ]
  · exfalso
    apply epsU_ne_one p
    have := h.1
    rwa [inv_one, one_mul] at this
  · exfalso
    apply epsU_ne_one p
    have := h.1
    rw [mul_one] at this
    exact inv_eq_one.mp this
  · obtain ⟨-, ⟨z, hz⟩, -⟩ := h
    congr 1
    symm
    apply crep_unique p c' c z
    have he : (epsP p : ℚ) ≠ 0 := epsP_ne_zero p
    simp only [inv_one, Units.val_one, vmul_one, Units.val_inv_eq_inv_val, epsU_val] at hz
    have h1 := congrArg Prod.fst hz
    have h2 := congrArg Prod.snd hz
    simp only [icast, cvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      neg_mul] at h1 h2
    field_simp at h1 h2
    push_cast at h1 h2
    ext
    · simp only [cvec, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      exact_mod_cast (by linarith : ((c'.1.val : ℚ) - c.1.val) = (epsP p : ℚ) * z.1)
    · simp only [cvec, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      exact_mod_cast (by linarith : ((c'.2.val : ℚ) - c.2.val) = (epsP p : ℚ) * z.2)

/-- **The explicit local correspondence at the good line.** -/
def goodLineCosets : LocalHecke.LocalCorrespondence Λ₁ where
  representatives := Finset.univ.image (rExpl p)
  stable := by
    intro g hg s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b, m, rfl⟩ := (mem_Λ₁_iff g).mp hg
    obtain ⟨i', hi'⟩ := rExpl_stable p b m i
    exact ⟨rExpl p i', Finset.mem_image_of_mem _ (Finset.mem_univ _), hi'⟩
  disjoint := by
    intro s hs s' hs' h
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hs'
    rw [rExpl_disjoint p i i' h]

theorem rExpl_mem (i : LIdx p) : rExpl p i ∈ (goodLineCosets p).representatives :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem rExpl_not_mem (i : LIdx p) : rExpl p i ∉ Λ₁ := by
  intro h
  rcases i with j | c <;> simp only [rExpl] at h <;> rw [Q_mem_iff] at h
  · obtain ⟨-, -, ⟨μ, hμ⟩⟩ := h
    have hdet := congrArg (fun g : GL (Fin 2) ℚ => (g : Matrix (Fin 2) (Fin 2) ℚ).det) hμ
    simp only [BGL_val, Bmat_det] at hdet
    have hmap : ((integralEmbed μ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        (((μ : Matrix (Fin 2) (Fin 2) ℤ).det : ℤ) : ℚ) :=
      (RingHom.map_det (Int.castRingHom ℚ) (μ : Matrix (Fin 2) (Fin 2) ℤ)).symm
    rw [hmap] at hdet
    have h2 : (p.val : ℚ) ≥ 2 := by exact_mod_cast p.property.two_le
    rcases det_units μ with h1 | h1 <;> rw [h1] at hdet <;> push_cast at hdet <;> linarith
  · exact epsU_ne_one p h.1

/-! ### Transitions -/

/-- `u(b) = Q(3b, 1, 1)` in `Λ₁`. -/
def U1 (b : ℤ × ℤ) : Λ₁ := ⟨Qint b 1, Qint_mem b 1⟩

/-- `diag(m, 1)` in `Λ₁`. -/
def L1 (m : GL (Fin 2) ℤ) : Λ₁ := ⟨Qint 0 m, Qint_mem 0 m⟩

/-- `Q(3b, m, 1)` in `Λ₁`. -/
def M1 (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) : Λ₁ := ⟨Qint b m, Qint_mem b m⟩

/-- The representative with index `i`. -/
def toRepL (i : LIdx p) : (goodLineCosets p).representatives := ⟨rExpl p i, rExpl_mem p i⟩

theorem next_inl (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    nextRep (goodLineCosets p) (M1 b m) (toRepL p (.inl j)) = toRepL p (.inl (arithmeticNext p m j)) := by
  apply nextRep_unique
  change (rExpl p (.inl j))⁻¹ * Qint b m * rExpl p (.inl (arithmeticNext p m j)) ∈ Λ₁
  rw [levi_product]
  exact Qint_mem _ _

theorem delta_inl (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    deltaRep (goodLineCosets p) (M1 b m) (toRepL p (.inl j)) =
      M1 (ivmul b (Bint p j)) (arithmeticDelta p m j) := by
  apply Subtype.ext
  rw [deltaRep_val, next_inl]
  exact levi_product p b m j

theorem next_inr (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) :
    nextRep (goodLineCosets p) (M1 b m) (toRepL p (.inr c)) =
      toRepL p (.inr (crep p (ivmul (cvec p c - b) m.val))) := by
  apply nextRep_unique
  change (rExpl p (.inr c))⁻¹ * Qint b m * rExpl p (.inr (crep p (ivmul (cvec p c - b) m.val))) ∈ Λ₁
  rw [radical_product]
  exact Qint_mem _ _

theorem delta_inr (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) :
    deltaRep (goodLineCosets p) (M1 b m) (toRepL p (.inr c)) =
      M1 (-ivmul (cq p (ivmul (cvec p c - b) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val) m := by
  apply Subtype.ext
  rw [deltaRep_val, next_inr]
  exact radical_product p b m c

/-! ### Residue arithmetic -/

theorem crep_add_eps (y w : ℤ × ℤ) : crep p (y + epsP p • w) = crep p y := by
  have hy := crep_spec p y
  conv_lhs => rw [hy]
  rw [add_assoc, ← smul_add, crep_cvec_add]

theorem cvec_crep (x : ℤ × ℤ) : cvec p (crep p x) = x - epsP p • cq p x :=
  eq_sub_of_add_eq (crep_spec p x).symm

theorem eps_smul_cq (x : ℤ × ℤ) : epsP p • cq p x = x - cvec p (crep p x) := by
  rw [cvec_crep]; abel

theorem epsP_ne_zero' : epsP p ≠ 0 := by
  intro h
  have := epsP_natAbs p
  rw [h] at this
  exact p.property.ne_zero this.symm

theorem eps_smul_injective {a b : ℤ × ℤ} (h : epsP p • a = epsP p • b) : a = b := by
  have he := epsP_ne_zero' p
  ext
  · have := congrArg Prod.fst h
    simp only [Prod.smul_fst, smul_eq_mul] at this
    exact mul_left_cancel₀ he this
  · have := congrArg Prod.snd h
    simp only [Prod.smul_snd, smul_eq_mul] at this
    exact mul_left_cancel₀ he this

theorem ivmul_injective (m : GL (Fin 2) ℤ) {a b : ℤ × ℤ} (h : ivmul a m.val = ivmul b m.val) : a = b := by
  have := congrArg (fun x => ivmul x (m⁻¹ : GL (Fin 2) ℤ).val) h
  simpa only [ivmul_inv_cancel] using this

theorem crep_levi_injective (m : GL (Fin 2) ℤ) :
    Function.Injective fun c : Fin p.val × Fin p.val => crep p (ivmul (cvec p c) m.val) := by
  intro c c' h
  simp only at h
  apply crep_unique p c c' (ivmul (cq p (ivmul (cvec p c) m.val) - cq p (ivmul (cvec p c') m.val))
    (m⁻¹ : GL (Fin 2) ℤ).val)
  apply ivmul_injective m
  rw [ivmul_sub, ivmul_smul, ivmul_cancel_inv, smul_sub, eps_smul_cq, eps_smul_cq, h]
  abel

theorem crep_levi_bijective (m : GL (Fin 2) ℤ) :
    Function.Bijective fun c : Fin p.val × Fin p.val => crep p (ivmul (cvec p c) m.val) :=
  Finite.injective_iff_bijective.mp (crep_levi_injective p m)

theorem crep_shift_injective (u : ℤ × ℤ) :
    Function.Injective fun c : Fin p.val × Fin p.val => crep p (cvec p c - u) := by
  intro c c' h
  simp only at h
  apply crep_unique p c c' (cq p (cvec p c - u) - cq p (cvec p c' - u))
  rw [smul_sub, eps_smul_cq, eps_smul_cq, h]
  abel

theorem crep_shift_bijective (u : ℤ × ℤ) :
    Function.Bijective fun c : Fin p.val × Fin p.val => crep p (cvec p c - u) :=
  Finite.injective_iff_bijective.mp (crep_shift_injective p u)

end TernaryPeriodPolynomials.Spectral.GoodLineCosets
