module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PlaneCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.AmbientHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneCosets

@[expose] public section


/-!
# The local `T_p`-cosets at the identity plane

For a prime `p ≠ 3`, put `εp = ±p ≡ 1 (mod 3)`, `B_j = p a_j⁻¹` (`a_j` the `GL₂` Hecke matrices of
`LevelOneCosets`) and let `w_{j,r}` (`0 ≤ r < p`) represent `ℤ² / B_j ℤ²`. The `1 + p(p+1)`
elements
`σ₀ = diag(1, 1, εp)` and `s_{j,r} = u(w_{j,r}) diag(B_j, 1)`
of the rational plane parabolic form a local correspondence of the identity-plane stabilizer
`Λ₀` (`identityPlaneCosets`): their cosets `sΛ₀` are distinct and permuted by left multiplication
by `Λ₀`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets

open PlaneCoordinates LevelOneCosets

variable (p : Nat.Primes)

/-! ### The sign `ε` with `εp ≡ 1 (mod 3)` -/

/-- `εp = ±p ≡ 1 (mod 3)`. -/
def epsP : ℤ := if (p.val : ℤ) % 3 = 1 then p.val else -(p.val : ℤ)

theorem epsP_mod (hp3 : p.val ≠ 3) : epsP p % 3 = 1 := by
  have h2 := p.property.two_le
  have hcop : ¬ (3 : ℤ) ∣ p.val := by
    intro h
    have : (3 : ℕ) ∣ p.val := by exact_mod_cast h
    rcases (Nat.dvd_prime p.property).mp this with h | h
    · omega
    · exact hp3 h.symm
  unfold epsP
  split_ifs with h
  · exact h
  · omega

theorem epsP_natAbs : (epsP p).natAbs = p.val := by
  unfold epsP
  split_ifs <;> simp

theorem epsP_ne_zero : (epsP p : ℚ) ≠ 0 := by
  have : epsP p ≠ 0 := by
    intro h
    have := epsP_natAbs p
    rw [h] at this
    exact p.property.ne_zero this.symm
  exact_mod_cast this

/-- `εp` as a unit of `ℚ`. -/
def epsU : ℚˣ := Units.mk0 (epsP p : ℚ) (epsP_ne_zero p)

theorem epsU_ne_one : epsU p ≠ 1 := by
  intro h
  have := congrArg Units.val h
  change (epsP p : ℚ) = 1 at this
  have h' : epsP p = 1 := by exact_mod_cast this
  have := epsP_natAbs p
  rw [h'] at this
  have := p.property.two_le
  simp at *
  omega

/-! ### The Levi matrices `B_j = p a_j⁻¹` -/

/-- `B_∞ = diag(1, p)`, `B_i = [[p, -i], [0, 1]]`. -/
def Bmat : Option (Fin p.val) → Matrix (Fin 2) (Fin 2) ℚ
  | none => !![1, 0; 0, (p.val : ℚ)]
  | some i => !![(p.val : ℚ), -(i.val : ℚ); 0, 1]

theorem Bmat_det (j : Option (Fin p.val)) : (Bmat p j).det = p.val := by
  cases j <;> simp [Bmat, Matrix.det_fin_two]

theorem p_ne_zero : (p.val : ℚ) ≠ 0 := by exact_mod_cast p.property.ne_zero

/-- `B_j` in `GL₂(ℚ)`. -/
def BGL (j : Option (Fin p.val)) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero (Bmat p j) (by rw [Bmat_det]; exact p_ne_zero p)

theorem BGL_val (j : Option (Fin p.val)) : (BGL p j).val = Bmat p j := rfl

/-- `B_j⁻¹ = a_j / p` as rational matrices. -/
theorem BGL_inv_val (j : Option (Fin p.val)) :
    ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val = (p.val : ℚ)⁻¹ • (M p j).map (Int.castRingHom ℚ) := by
  have hp := p_ne_zero p
  have h : (BGL p j).val * ((p.val : ℚ)⁻¹ • (M p j).map (Int.castRingHom ℚ)) = 1 := by
    rw [BGL_val]
    cases j with
    | none =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Bmat, M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
    | some i =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Bmat, M, modularHeckeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> (field_simp; try ring)
  calc ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val
      = ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val *
          ((BGL p j).val * ((p.val : ℚ)⁻¹ • (M p j).map (Int.castRingHom ℚ))) := by rw [h, mul_one]
    _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- The `GL₂` transitions in terms of `B_j`: `B_j⁻¹ m = μ B_k⁻¹`. -/
theorem levi_transition (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    (BGL p j)⁻¹ * integralEmbed m =
      integralEmbed (arithmeticDelta p m j) * (BGL p (arithmeticNext p m j))⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, BGL_inv_val, BGL_inv_val, integralEmbed_val, integralEmbed_val,
    Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, arithmeticDelta_spec]

/-! ### Integral vectors and coset representatives of `ℤ² / B_j ℤ²` -/

/-- Integral vectors. -/
def IsInt (x : ℚ × ℚ) : Prop := ∃ c : ℤ × ℤ, x = ((c.1 : ℚ), (c.2 : ℚ))

/-- The cast of an integral vector. -/
def icast (b : ℤ × ℤ) : ℚ × ℚ := ((b.1 : ℚ), (b.2 : ℚ))

@[simp] theorem icast_zero : icast 0 = 0 := by simp [icast]

theorem icast_add (b c : ℤ × ℤ) : icast (b + c) = icast b + icast c := by
  simp [icast]

theorem icast_sub (b c : ℤ × ℤ) : icast (b - c) = icast b - icast c := by
  simp [icast]

theorem icast_neg (b : ℤ × ℤ) : icast (-b) = -icast b := by
  simp [icast]

theorem icast_injective : Function.Injective icast := by
  intro b c h
  simp only [icast, Prod.mk.injEq] at h
  ext
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- Integral matrix–vector product. -/
def imul (m : Matrix (Fin 2) (Fin 2) ℤ) (b : ℤ × ℤ) : ℤ × ℤ :=
  (m 0 0 * b.1 + m 0 1 * b.2, m 1 0 * b.1 + m 1 1 * b.2)

theorem bmul_icast (m : Matrix (Fin 2) (Fin 2) ℤ) (b : ℤ × ℤ) :
    bmul (m.map (Int.castRingHom ℚ)) (icast b) = icast (imul m b) := by
  simp [bmul, imul, icast]

/-- The representatives `w_{∞,r} = (0, r)`, `w_{i,r} = (r, 0)`. -/
def wint : Option (Fin p.val) → Fin p.val → ℤ × ℤ
  | none, r => (0, r.val)
  | some _, r => (r.val, 0)

/-- The representative index of `b` modulo `B_j ℤ²`. -/
def repIdx : Option (Fin p.val) → ℤ × ℤ → Fin p.val
  | none, b => ⟨(b.2 % (p.val : ℤ)).toNat, by
      have h1 := Int.emod_nonneg b.2 (by exact_mod_cast p.property.ne_zero : (p.val : ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos b.2 (by exact_mod_cast p.property.pos : (0 : ℤ) < p.val)
      omega⟩
  | some i, b => ⟨((b.1 + i.val * b.2) % (p.val : ℤ)).toNat, by
      have h1 := Int.emod_nonneg (b.1 + i.val * b.2)
        (by exact_mod_cast p.property.ne_zero : (p.val : ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos (b.1 + i.val * b.2)
        (by exact_mod_cast p.property.pos : (0 : ℤ) < p.val)
      omega⟩

/-- The integral vector `B_j⁻¹ (b - w_{j, rep b})`. -/
def quotVec : Option (Fin p.val) → ℤ × ℤ → ℤ × ℤ
  | none, b => (b.1, b.2 / (p.val : ℤ))
  | some i, b => ((b.1 + i.val * b.2) / (p.val : ℤ), b.2)

theorem toNat_emod (z : ℤ) : (((z % (p.val : ℤ)).toNat : ℕ) : ℤ) = z % (p.val : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (by exact_mod_cast p.property.ne_zero))

theorem bmul_BGL_inv_none (x : ℚ × ℚ) :
    bmul ((BGL p none)⁻¹ : GL (Fin 2) ℚ).val x = (x.1, x.2 / p.val) := by
  have hp := p_ne_zero p
  rw [BGL_inv_val]
  simp only [bmul, M, modularHeckeMatrix, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  ext <;> simp <;> field_simp

theorem bmul_BGL_inv_some (i : Fin p.val) (x : ℚ × ℚ) :
    bmul ((BGL p (some i))⁻¹ : GL (Fin 2) ℚ).val x = ((x.1 + i.val * x.2) / p.val, x.2) := by
  have hp := p_ne_zero p
  rw [BGL_inv_val]
  simp only [bmul, M, modularHeckeMatrix, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  ext <;> simp <;> field_simp

/-- **`b ≡ w_{j, rep b}` modulo `B_j ℤ²`.** -/
theorem rep_spec (j : Option (Fin p.val)) (b : ℤ × ℤ) :
    bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast (b - wint p j (repIdx p j b))) =
      icast (quotVec p j b) := by
  have hp := p_ne_zero p
  cases j with
  | none =>
    rw [bmul_BGL_inv_none]
    have hdiv := Int.emod_add_mul_ediv b.2 (p.val : ℤ)
    have hdivQ : (b.2 : ℚ) - ((b.2 % (p.val : ℤ) : ℤ) : ℚ) = (p.val : ℚ) * ((b.2 / (p.val : ℤ) : ℤ) : ℚ) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hdiv
      push_cast at this ⊢
      linarith
    simp only [icast, wint, repIdx, quotVec, Prod.fst_sub, Prod.snd_sub, toNat_emod, Int.cast_sub,
      sub_zero]
    ext
    · rfl
    · simp only
      rw [hdivQ]
      field_simp
  | some i =>
    rw [bmul_BGL_inv_some]
    have hdiv := Int.emod_add_mul_ediv (b.1 + i.val * b.2) (p.val : ℤ)
    have hdivQ : (b.1 : ℚ) - (((b.1 + i.val * b.2) % (p.val : ℤ) : ℤ) : ℚ) + (i.val : ℚ) * (b.2 : ℚ) =
        (p.val : ℚ) * (((b.1 + i.val * b.2) / (p.val : ℤ) : ℤ) : ℚ) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hdiv
      push_cast at this ⊢
      linarith
    simp only [icast, wint, repIdx, quotVec, Prod.fst_sub, Prod.snd_sub, toNat_emod, Int.cast_sub,
      sub_zero]
    ext
    · simp only
      rw [hdivQ]
      field_simp
    · rfl

theorem isInt_icast (b : ℤ × ℤ) : IsInt (icast b) := ⟨b, rfl⟩

/-- Distinct representatives are incongruent. -/
theorem rep_unique (j : Option (Fin p.val)) (r r' : Fin p.val)
    (h : IsInt (bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast (wint p j r - wint p j r')))) :
    r = r' := by
  have hp := p_ne_zero p
  obtain ⟨c, hc⟩ := h
  have key : ∃ z : ℤ, ((r.val : ℤ) - r'.val) = p.val * z := by
    cases j with
    | none =>
      rw [bmul_BGL_inv_none] at hc
      simp only [icast, wint, Prod.fst_sub, Prod.snd_sub, Prod.mk.injEq] at hc
      refine ⟨c.2, ?_⟩
      have h2 := hc.2
      field_simp at h2
      push_cast at h2 ⊢
      exact_mod_cast (by linarith : ((r.val : ℚ) - r'.val) = p.val * c.2)
    | some i =>
      rw [bmul_BGL_inv_some] at hc
      simp only [icast, wint, Prod.fst_sub, Prod.snd_sub, Prod.mk.injEq] at hc
      refine ⟨c.1, ?_⟩
      have h1 := hc.1
      simp only [Int.cast_zero, sub_zero, mul_zero, add_zero] at h1
      field_simp at h1
      push_cast at h1 ⊢
      exact_mod_cast (by linarith : ((r.val : ℚ) - r'.val) = p.val * c.1)
  obtain ⟨z, hz⟩ := key
  have hr := r.isLt
  have hr' := r'.isLt
  have hzero := Int.eq_zero_of_abs_lt_dvd (⟨z, hz⟩ : (p.val : ℤ) ∣ (r.val : ℤ) - r'.val)
    (by rw [abs_lt]; constructor <;> omega)
  apply Fin.ext
  omega

theorem isInt_add {x y : ℚ × ℚ} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by simp⟩

theorem isInt_neg {x : ℚ × ℚ} (hx : IsInt x) : IsInt (-x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by simp⟩

theorem isInt_sub {x y : ℚ × ℚ} (hx : IsInt x) (hy : IsInt y) : IsInt (x - y) := by
  rw [sub_eq_add_neg]
  exact isInt_add hx (isInt_neg hy)

/-- If `b ≡ w_{j,r}` then `r` is the representative index of `b`. -/
theorem eq_repIdx (j : Option (Fin p.val)) (r : Fin p.val) (b : ℤ × ℤ)
    (h : IsInt (bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast (b - wint p j r)))) :
    r = repIdx p j b := by
  apply rep_unique p j
  have h2 := rep_spec p j b
  have : icast (wint p j r - wint p j (repIdx p j b)) =
      icast (b - wint p j (repIdx p j b)) - icast (b - wint p j r) := by
    simp only [icast_sub]; abel
  rw [this, bmul_sub, h2]
  exact isInt_sub (isInt_icast _) h

/-- `B_j⁻¹ = p⁻¹ a_j`. -/
theorem BGL_inv_eq (j : Option (Fin p.val)) :
    (BGL p j)⁻¹ = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p.val : ℚ) (p_ne_zero p))⁻¹ *
      binaryHeckeRepresentative p j := by
  apply Units.ext
  rw [BGL_inv_val, Units.val_mul, rep_val]
  ext a b
  simp [GeneralLinearGroup.scalar, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply]

/-- Distinct indices give distinct lattices `B_j ℤ²`. -/
theorem BGL_unique {j j' : Option (Fin p.val)} {μ : GL (Fin 2) ℤ}
    (h : (BGL p j)⁻¹ * BGL p j' = integralEmbed μ) : j = j' := by
  apply (arithmeticCosets p).disjoint j j' μ
  rw [← h, arithmeticCosets_rep]
  have e1 := BGL_inv_eq p j
  have e2 : BGL p j' = (binaryHeckeRepresentative p j')⁻¹ *
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p.val : ℚ) (p_ne_zero p)) := by
    rw [← inv_inv (BGL p j'), BGL_inv_eq, _root_.mul_inv_rev, ← map_inv, inv_inv]
  rw [e1, e2, mul_assoc, ← mul_assoc (binaryHeckeRepresentative p j),
    ← GeneralLinearGroup.scalar_commute, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel,
    map_one, one_mul]

/-! ### The explicit local correspondence -/

theorem P_mem_of {x : ℚ × ℚ} {B : GL (Fin 2) ℚ} {d : ℚˣ} (hd : d = 1) (hx : IsInt x)
    (hB : ∃ μ : GL (Fin 2) ℤ, B = integralEmbed μ) : P x B d ∈ Λ₀ := by
  obtain ⟨b, rfl⟩ := hx
  obtain ⟨μ, rfl⟩ := hB
  subst hd
  exact Pint_mem b μ

theorem Pint_eq (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) : Pint b m = P (icast b) (integralEmbed m) 1 := rfl

theorem mem_Λ₀_iff' (g : RationalGL3) : g ∈ Λ₀ ↔ ∃ b m, g = P (icast b) (integralEmbed m) 1 :=
  mem_Λ₀_iff g

theorem bmul_zero (B : Matrix (Fin 2) (Fin 2) ℚ) : bmul B 0 = 0 := by simp [bmul]

theorem bmul_integralEmbed (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    bmul (integralEmbed m).val (icast b) = icast (imul m.val b) := by
  rw [integralEmbed_val, bmul_icast]

theorem integralEmbed_inv_val (m : GL (Fin 2) ℤ) :
    ((integralEmbed m)⁻¹ : GL (Fin 2) ℚ).val = (m⁻¹ : GL (Fin 2) ℤ).val.map (Int.castRingHom ℚ) := by
  rw [← map_inv, integralEmbed_val]

theorem icast_smul_int (z : ℤ) (b : ℤ × ℤ) : (z : ℚ) • icast b = icast (z • b) := by
  simp [icast]

/-- The index type `{σ₀} ⊔ {(j, r)}`. -/
abbrev SIdx := Option (Option (Fin p.val) × Fin p.val)

/-- The explicit elements `σ₀ = P(0, 1, εp)` and `s_{j,r} = P(w_{j,r}, B_j, 1)`. -/
def sExpl : SIdx p → RationalGL3
  | none => P 0 1 (epsU p)
  | some (j, r) => P (icast (wint p j r)) (BGL p j) 1

theorem BGL_injective {j j' : Option (Fin p.val)} (h : BGL p j = BGL p j') : j = j' :=
  BGL_unique p (μ := 1) (by rw [h, inv_mul_cancel, map_one])

theorem sExpl_injective : Function.Injective (sExpl p) := by
  intro i i' h
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some jr =>
      obtain ⟨-, -, hd⟩ := P_injective h
      exact absurd hd (epsU_ne_one p)
  | some jr =>
    cases i' with
    | none =>
      obtain ⟨-, -, hd⟩ := P_injective h
      exact absurd hd.symm (epsU_ne_one p)
    | some jr' =>
      obtain ⟨j, r⟩ := jr
      obtain ⟨j', r'⟩ := jr'
      obtain ⟨hw, hB, -⟩ := P_injective h
      have hj := BGL_injective p hB
      subst hj
      have hr : r = r' := by
        apply rep_unique p j
        rw [icast_sub, hw, sub_self, bmul_zero]
        exact ⟨0, rfl⟩
      rw [hr]

theorem epsU_val : ((epsU p : ℚˣ) : ℚ) = (epsP p : ℚ) := rfl

/-- The `GL₂` transition used for stability: `a_{j'} m = μ a_j` with `j' = next⁻¹ j`. -/
def prevIdx (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) : Option (Fin p.val) :=
  ((arithmeticCosets p).nextEquiv m).symm j

theorem next_prevIdx (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    arithmeticNext p m (prevIdx p m j) = j :=
  ((arithmeticCosets p).nextEquiv m).apply_symm_apply j

theorem one_smul_vec (x : ℚ × ℚ) : ((1 : ℚˣ) : ℚ) • x = x := by simp

/-- **Stability** of the explicit cosets under `Λ₀`. -/
theorem sExpl_stable (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (i : SIdx p) :
    ∃ i' : SIdx p, (sExpl p i')⁻¹ * (P (icast b) (integralEmbed m) 1 * sExpl p i) ∈ Λ₀ := by
  cases i with
  | none =>
    refine ⟨none, ?_⟩
    simp only [sExpl]
    rw [P_inv, P_mul, P_mul]
    apply P_mem_of
    · simp
    · refine ⟨epsP p • b, ?_⟩
      simp [bmul_zero, bmul_one, icast, epsU_val]
    · exact ⟨m, by simp⟩
  | some jr =>
    obtain ⟨j, r⟩ := jr
    refine ⟨some (prevIdx p m j, repIdx p (prevIdx p m j) (b + imul m.val (wint p j r))), ?_⟩
    simp only [sExpl]
    rw [P_inv, P_mul, P_mul]
    apply P_mem_of
    · simp
    · have h := rep_spec p (prevIdx p m j) (b + imul m.val (wint p j r))
      refine ⟨quotVec p (prevIdx p m j) (b + imul m.val (wint p j r)), ?_⟩
      simp only [inv_one, Units.val_one, one_smul, neg_smul]
      change _ = icast _
      rw [← h, icast_sub, icast_add, bmul_sub, ← bmul_icast, ← integralEmbed_val]
      simp only [bmul_add]
      abel
    · refine ⟨arithmeticDelta p m (prevIdx p m j), ?_⟩
      have h := levi_transition p m (prevIdx p m j)
      rw [next_prevIdx] at h
      rw [← mul_assoc, h, mul_assoc, inv_mul_cancel, mul_one]

/-- **Disjointness** of the explicit cosets. -/
theorem sExpl_disjoint (i i' : SIdx p) (h : (sExpl p i)⁻¹ * sExpl p i' ∈ Λ₀) : i = i' := by
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some jr =>
      exfalso
      simp only [sExpl] at h
      rw [P_inv, P_mul, P_mem_iff] at h
      apply epsU_ne_one p
      have := h.1
      rw [mul_one] at this
      exact inv_eq_one.mp this
  | some jr =>
    obtain ⟨j, r⟩ := jr
    cases i' with
    | none =>
      exfalso
      simp only [sExpl] at h
      rw [P_inv, P_mul, P_mem_iff] at h
      apply epsU_ne_one p
      have := h.1
      rwa [inv_one, one_mul] at this
    | some jr' =>
      obtain ⟨j', r'⟩ := jr'
      simp only [sExpl] at h
      rw [P_inv, P_mul, P_mem_iff] at h
      obtain ⟨-, hx, ⟨μ, hμ⟩⟩ := h
      have hj := BGL_unique p hμ
      subst hj
      have hr : r' = r := by
        apply rep_unique p j
        rw [icast_sub, bmul_sub]
        obtain ⟨c, hc⟩ := hx
        refine ⟨c, ?_⟩
        rw [← hc]
        simp only [Units.val_one, neg_smul, one_smul, inv_one]
        abel
      rw [hr]

/-- **The explicit local correspondence at the identity plane.** -/
def identityPlaneCosets : LocalHecke.LocalCorrespondence Λ₀ where
  representatives := Finset.univ.image (sExpl p)
  stable := by
    intro g hg s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b, m, rfl⟩ := (mem_Λ₀_iff' g).mp hg
    obtain ⟨i', hi'⟩ := sExpl_stable p b m i
    exact ⟨sExpl p i', Finset.mem_image_of_mem _ (Finset.mem_univ _), hi'⟩
  disjoint := by
    intro s hs s' hs' h
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hs'
    rw [sExpl_disjoint p i i' h]

theorem sExpl_mem (i : SIdx p) : sExpl p i ∈ (identityPlaneCosets p).representatives :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- No explicit representative lies in `Λ₀`. -/
theorem sExpl_not_mem (i : SIdx p) : sExpl p i ∉ Λ₀ := by
  intro h
  cases i with
  | none =>
    simp only [sExpl] at h
    rw [P_mem_iff] at h
    exact epsU_ne_one p h.1
  | some jr =>
    obtain ⟨j, r⟩ := jr
    simp only [sExpl] at h
    rw [P_mem_iff] at h
    obtain ⟨-, -, ⟨μ, hμ⟩⟩ := h
    have hdet := congrArg (fun g : GL (Fin 2) ℚ => (g : Matrix (Fin 2) (Fin 2) ℚ).det) hμ
    simp only [BGL_val, Bmat_det] at hdet
    have hmap : ((GeneralLinearGroup.map (Int.castRingHom ℚ) μ : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det = (((μ : Matrix (Fin 2) (Fin 2) ℤ).det : ℤ) : ℚ) :=
      (RingHom.map_det (Int.castRingHom ℚ) (μ : Matrix (Fin 2) (Fin 2) ℤ)).symm
    rw [hmap] at hdet
    have h2 : (p.val : ℚ) ≥ 2 := by exact_mod_cast p.property.two_le
    rcases det_units μ with h1 | h1 <;> rw [h1] at hdet <;> push_cast at hdet <;> linarith

/-! ### Explicit transitions -/

open AmbientHecke

/-- The radical element `u(b)` of `Λ₀`. -/
def Uel (b : ℤ × ℤ) : Λ₀ := ⟨Pint b 1, Pint_mem b 1⟩

/-- The Levi element `diag(m, 1)` of `Λ₀`. -/
def Lel (m : GL (Fin 2) ℤ) : Λ₀ := ⟨Pint 0 m, Pint_mem 0 m⟩

/-- The mixed element `u(b) diag(m, 1)` of `Λ₀`. -/
def Mel (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) : Λ₀ := ⟨Pint b m, Pint_mem b m⟩

/-- The representative with index `i`. -/
def toRep (i : SIdx p) : (identityPlaneCosets p).representatives := ⟨sExpl p i, sExpl_mem p i⟩

theorem toRep_val (i : SIdx p) : (toRep p i).val = sExpl p i := rfl

/-- Transition of `σ₀` under any element. -/
theorem next_none (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) :
    nextRep (identityPlaneCosets p) (Mel b m) (toRep p none) = toRep p none := by
  apply nextRep_unique
  change (sExpl p none)⁻¹ * P (icast b) (integralEmbed m) 1 * sExpl p none ∈ Λ₀
  rw [mul_assoc]
  simp only [sExpl]
  rw [P_inv, P_mul, P_mul]
  apply P_mem_of
  · simp
  · refine ⟨epsP p • b, ?_⟩
    simp [bmul_zero, bmul_one, icast, epsU_val]
  · exact ⟨m, by simp⟩

theorem delta_none (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) :
    deltaRep (identityPlaneCosets p) (Mel b m) (toRep p none) = Mel (epsP p • b) m := by
  apply Subtype.ext
  rw [deltaRep_val, next_none]
  change (sExpl p none)⁻¹ * P (icast b) (integralEmbed m) 1 * sExpl p none =
    P (icast (epsP p • b)) (integralEmbed m) 1
  simp only [sExpl]
  rw [P_inv, P_mul, P_mul]
  congr 1
  · simp [bmul_zero, bmul_one, icast, epsU_val]
  · simp
  · simp

/-- The next index of `(j, r)` under `u(b) diag(m, 1)`. -/
def nextIdx (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    Option (Fin p.val) × Fin p.val :=
  (arithmeticNext p m j,
    repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r - b)))

/-- The radical part `q = B_k⁻¹ (m⁻¹(w - b) - w')` of the transition. -/
def transVec (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) : ℤ × ℤ :=
  quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r - b))

theorem levi_transition' (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    (BGL p j)⁻¹ = integralEmbed (arithmeticDelta p m j) * (BGL p (arithmeticNext p m j))⁻¹ *
      (integralEmbed m)⁻¹ := by
  rw [← levi_transition, mul_inv_cancel_right]

theorem imul_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (b : ℤ × ℤ) :
    imul (A * B) b = imul A (imul B b) := by
  simp only [imul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp <;> ring

theorem imul_sub (A : Matrix (Fin 2) (Fin 2) ℤ) (b c : ℤ × ℤ) :
    imul A (b - c) = imul A b - imul A c := by
  simp only [imul, Prod.fst_sub, Prod.snd_sub]
  ext <;> simp <;> ring

theorem imul_neg (A : Matrix (Fin 2) (Fin 2) ℤ) (b : ℤ × ℤ) : imul A (-b) = -imul A b := by
  simp only [imul, Prod.fst_neg, Prod.snd_neg]
  ext <;> simp <;> ring

theorem imul_one (b : ℤ × ℤ) : imul 1 b = b := by
  simp [imul]

/-- The transition vector identity `B_j⁻¹ (b - w + m w') = -μ q`. -/
theorem trans_vector (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    -bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast (wint p j r)) +
        bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val
          (icast b + bmul (integralEmbed m).val (icast (wint p (nextIdx p b m j r).1
            (nextIdx p b m j r).2))) =
      icast (-imul (arithmeticDelta p m j).val (transVec p b m j r)) := by
  have hrep := rep_spec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r - b))
  have hx : icast (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r - b)) =
      bmul ((integralEmbed m)⁻¹ : GL (Fin 2) ℚ).val (icast (wint p j r - b)) := by
    rw [integralEmbed_inv_val, bmul_icast]
  simp only [nextIdx, transVec]
  set w'' := wint p (arithmeticNext p m j)
    (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r - b)))
  set q := quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r - b))
  set x := imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r - b)
  rw [icast_sub, bmul_sub] at hrep
  calc -bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast (wint p j r)) +
        bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val (icast b + bmul (integralEmbed m).val (icast w''))
      = bmul ((BGL p j)⁻¹ : GL (Fin 2) ℚ).val
          (icast b + bmul (integralEmbed m).val (icast w'') - icast (wint p j r)) := by
        rw [bmul_sub]; abel
    _ = bmul (integralEmbed (arithmeticDelta p m j)).val
          (bmul ((BGL p (arithmeticNext p m j))⁻¹ : GL (Fin 2) ℚ).val
            (bmul ((integralEmbed m)⁻¹ : GL (Fin 2) ℚ).val
              (icast b + bmul (integralEmbed m).val (icast w'') - icast (wint p j r)))) := by
        rw [levi_transition' p m j, Units.val_mul, Units.val_mul, bmul_mul, bmul_mul]
    _ = bmul (integralEmbed (arithmeticDelta p m j)).val
          (bmul ((BGL p (arithmeticNext p m j))⁻¹ : GL (Fin 2) ℚ).val (icast w'' - icast x)) := by
        congr 2
        rw [hx, bmul_sub, bmul_add, bmul_inv_cancel, icast_sub, bmul_sub]
        abel
    _ = bmul (integralEmbed (arithmeticDelta p m j)).val (-icast q) := by
        rw [bmul_sub, ← hrep, neg_sub]
    _ = icast (-imul (arithmeticDelta p m j).val q) := by
        rw [bmul_neg, bmul_integralEmbed, icast_neg]

theorem trans_levi (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    (BGL p j)⁻¹ * (integralEmbed m * BGL p (arithmeticNext p m j)) =
      integralEmbed (arithmeticDelta p m j) := by
  rw [← mul_assoc, levi_transition, mul_assoc, inv_mul_cancel, mul_one]

theorem trans_product (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    (sExpl p (some (j, r)))⁻¹ * P (icast b) (integralEmbed m) 1 *
        sExpl p (some (nextIdx p b m j r)) =
      Pint (-imul (arithmeticDelta p m j).val (transVec p b m j r)) (arithmeticDelta p m j) := by
  simp only [sExpl]
  rw [P_inv, P_mul, P_mul, Pint_eq]
  congr 1
  · simp only [Units.val_one, one_smul, neg_smul, inv_one, mul_one, Units.val_mul, bmul_mul]
    rw [add_assoc, ← bmul_add]
    exact trans_vector p b m j r
  · rw [mul_assoc]
    exact trans_levi p m j
  · simp

/-- Transition of `s_{j,r}`. -/
theorem next_some (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    nextRep (identityPlaneCosets p) (Mel b m) (toRep p (some (j, r))) =
      toRep p (some (nextIdx p b m j r)) := by
  apply nextRep_unique
  change (sExpl p (some (j, r)))⁻¹ * P (icast b) (integralEmbed m) 1 *
    sExpl p (some (nextIdx p b m j r)) ∈ Λ₀
  rw [trans_product]
  exact Pint_mem _ _

theorem delta_some (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    deltaRep (identityPlaneCosets p) (Mel b m) (toRep p (some (j, r))) =
      Mel (-imul (arithmeticDelta p m j).val (transVec p b m j r)) (arithmeticDelta p m j) := by
  apply Subtype.ext
  rw [deltaRep_val, next_some]
  exact trans_product p b m j r

/-! ### Vector identities for the transitions -/

theorem rep_spec' (k : Option (Fin p.val)) (x : ℤ × ℤ) :
    icast x = icast (wint p k (repIdx p k x)) + bmul (BGL p k).val (icast (quotVec p k x)) := by
  rw [← rep_spec p k x, bmul_cancel_inv, icast_sub]
  abel

theorem bmul_injective (B : GL (Fin 2) ℚ) {x y : ℚ × ℚ} (h : bmul B.val x = bmul B.val y) : x = y := by
  have := congrArg (bmul (B⁻¹ : GL (Fin 2) ℚ).val) h
  rwa [bmul_inv_cancel, bmul_inv_cancel] at this

/-- `B_j μ = m B_k`. -/
theorem BGL_mul_delta (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    BGL p j * integralEmbed (arithmeticDelta p m j) = integralEmbed m * BGL p (arithmeticNext p m j) := by
  have h := levi_transition p m j
  rw [eq_mul_inv_iff_mul_eq] at h
  rw [← h]
  group

theorem bmul_BGL_delta (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (y : ℚ × ℚ) :
    bmul (BGL p j).val (bmul (integralEmbed (arithmeticDelta p m j)).val y) =
      bmul (integralEmbed m).val (bmul (BGL p (arithmeticNext p m j)).val y) := by
  rw [← bmul_mul, ← bmul_mul, ← Units.val_mul, ← Units.val_mul, BGL_mul_delta]

theorem icast_imul (A : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    icast (imul A.val b) = bmul (integralEmbed A).val (icast b) := (bmul_integralEmbed A b).symm

theorem integralEmbed_inv (m : GL (Fin 2) ℤ) : integralEmbed m⁻¹ = (integralEmbed m)⁻¹ := map_inv _ _

theorem imul_inv_cancel' (μ : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    imul (μ⁻¹ : GL (Fin 2) ℤ).val (imul μ.val y) = y := by
  rw [← imul_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, imul_one]

theorem imul_cancel_inv' (μ : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    imul μ.val (imul (μ⁻¹ : GL (Fin 2) ℤ).val y) = y := by
  rw [← imul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, imul_one]

end TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets
