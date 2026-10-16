module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.PrimeCount
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.CentralWeight

@[expose] public section


/-!
# The Hecke correspondence `diag(p, p, 1)` on plane sections

`x ∈ GL₃(ℤ) diag(p,p,1) GL₃(ℤ)` if and only if `p x⁻¹ ∈ GL₃(ℤ) diag(p,1,1) GL₃(ℤ)`. A plane datum
`(B, s)`, `s > 0`, of this double coset has either `s = 1` and `B ∈ p · GL₂(ℤ)`, or `s = p` and `B`
integral of determinant `±p`. The plane eigenvalue is `p² W(p·1, 1) + (p + 1) W(diag(p,1), p)`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n p : ℕ}

/-- `diag(p, p, 1)` in `GL₃(ℚ)`. -/
def gP2 (hp : p.Prime) : RationalGL3 :=
  ⟨diagonal ![(p : ℚ), p, 1], diagonal ![(p : ℚ)⁻¹, (p : ℚ)⁻¹, 1], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    fin_cases i <;> simp [this], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    fin_cases i <;> simp [this]⟩

theorem gP2_val_int (hp : p.Prime) :
    (gP2 hp).val = (diagonal ![(p : ℤ), p, 1]).map (Int.cast : ℤ → ℚ) := by
  change diagonal ![(p : ℚ), p, 1] = _
  rw [diagonal_map (by simp)]
  congr 1; funext i; fin_cases i <;> simp

/-- The permutation matrix exchanging the first and last coordinates. -/
def swap02 : RationalGL3 :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem swap02_val : swap02.val = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

theorem swap02_Γ : swap02 ∈ Γ := by
  have h : (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℤ) *
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨intUnit _ _ h, ?_⟩
  apply Units.ext
  rw [intUnit_val, swap02_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem swap_gP (hp : p.Prime) : swap02 * gP hp * swap02 = pScalar hp * (gP2 hp)⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, swap02_val, pScalar_val,
    show (gP hp).val = diagonal ![(p : ℚ), 1, 1] from rfl,
    show ((gP2 hp)⁻¹).val = diagonal ![(p : ℚ)⁻¹, (p : ℚ)⁻¹, 1] from rfl]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.vecMul_diagonal, hp0]

theorem swap_gP2 (hp : p.Prime) : swap02 * gP2 hp * swap02 = pScalar hp * (gP hp)⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, swap02_val, pScalar_val,
    show (gP2 hp).val = diagonal ![(p : ℚ), p, 1] from rfl,
    show ((gP hp)⁻¹).val = diagonal ![(p : ℚ)⁻¹, 1, 1] from rfl]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.vecMul_diagonal, hp0]

/-- **Duality of the two prime double cosets.** -/
theorem mem_DZ_gP2_iff (hp : p.Prime) (x : RationalGL3) :
    x ∈ DZ (gP2 hp) ↔ pScalar hp * x⁻¹ ∈ DZ (gP hp) := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨b⁻¹ * swap02, Γ.mul_mem (Γ.inv_mem hb) swap02_Γ, swap02 * a⁻¹,
      Γ.mul_mem swap02_Γ (Γ.inv_mem ha), ?_⟩
    have e := pScalar_central hp b⁻¹
    calc pScalar hp * (a * gP2 hp * b)⁻¹ = pScalar hp * b⁻¹ * ((gP2 hp)⁻¹ * a⁻¹) := by group
      _ = b⁻¹ * (pScalar hp * (gP2 hp)⁻¹) * a⁻¹ := by rw [e]; group
      _ = b⁻¹ * swap02 * gP hp * (swap02 * a⁻¹) := by rw [← swap_gP hp]; group
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨b⁻¹ * swap02, Γ.mul_mem (Γ.inv_mem hb) swap02_Γ, swap02 * a⁻¹,
      Γ.mul_mem swap02_Γ (Γ.inv_mem ha), ?_⟩
    have hxinv : x⁻¹ = (pScalar hp)⁻¹ * (a * gP hp * b) := by
      rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]
    have e1 := pScalar_central hp a⁻¹
    have e2 := pScalar_central hp (gP hp)⁻¹
    calc x = (x⁻¹)⁻¹ := (inv_inv x).symm
      _ = ((pScalar hp)⁻¹ * (a * gP hp * b))⁻¹ := by rw [hxinv]
      _ = b⁻¹ * (gP hp)⁻¹ * (a⁻¹ * pScalar hp) := by group
      _ = b⁻¹ * ((gP hp)⁻¹ * pScalar hp) * a⁻¹ := by rw [← e1]; group
      _ = b⁻¹ * (pScalar hp * (gP hp)⁻¹) * a⁻¹ := by rw [← e2]
      _ = b⁻¹ * swap02 * gP2 hp * (swap02 * a⁻¹) := by rw [← swap_gP2 hp]; group

/-- Elements of the double coset of `diag(p,p,1)` are integral. -/
theorem DZ_gP2_int (hp : p.Prime) {x : RationalGL3} (hx : x ∈ DZ (gP2 hp)) :
    ∀ i j, ∃ z : ℤ, (z : ℚ) = x.val i j := by
  obtain ⟨_, ⟨a₀, rfl⟩, _, ⟨b₀, rfl⟩, rfl⟩ := hx
  have hval : (integralRational a₀ * gP2 hp * integralRational b₀).val =
      (a₀.val * diagonal ![(p : ℤ), p, 1] * b₀.val).map (Int.cast : ℤ → ℚ) := by
    rw [Units.val_mul, Units.val_mul, gP2_val_int, intCast_map_mul3, intCast_map_mul3]
    rfl
  rw [hval]
  exact fun i j => ⟨_, rfl⟩

theorem levi_plane_inv (v : ℚ × ℚ) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    (pU v * planeLevi B s)⁻¹ = planeLevi B⁻¹ s⁻¹ * pU (-v) := by
  rw [_root_.mul_inv_rev, pU_neg]
  congr 1

theorem levi_pU_val (C : GeneralLinearGroup (Fin 2) ℚ) (t : ℚˣ) (w : ℚ × ℚ) :
    (planeLevi C t * pU w).val =
      !![C.val 0 0, C.val 0 1, C.val 0 0 * w.1 + C.val 0 1 * w.2;
        C.val 1 0, C.val 1 1, C.val 1 0 * w.1 + C.val 1 1 * w.2; 0, 0, (t : ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pU, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem plane_det (v : ℚ × ℚ) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    (pU v * planeLevi B s).val.det = B.val.det * s := by
  rw [plane_val, det_fin_three, det_fin_two]
  simp
  ring

theorem det_pScalar_mul_inv (hp : p.Prime) (x : RationalGL3) :
    (pScalar hp * x⁻¹).val.det = (p : ℚ) ^ 3 * (x.val.det)⁻¹ := by
  have hx : (x⁻¹).val.det * x.val.det = 1 := by
    rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  have hx0 : x.val.det ≠ 0 := by
    intro h; rw [h, mul_zero] at hx; exact zero_ne_one hx
  rw [Units.val_mul, det_mul, pScalar_val, det_smul, det_one, mul_one, Fintype.card_fin]
  rw [eq_inv_of_mul_eq_one_left hx]

theorem det_inv2 (B : GeneralLinearGroup (Fin 2) ℚ) : (B⁻¹).val.det = (B.val.det)⁻¹ := by
  have hx : (B⁻¹).val.det * B.val.det = 1 := by
    rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  exact eq_inv_of_mul_eq_one_left hx

/-- **Plane Levi data of the double coset of `diag(p,p,1)`.** -/
theorem prime2_plane_levi (hp : p.Prime) (v : ℚ × ℚ) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ)
    (hs : 0 < (s : ℚ)) (h : pU v * planeLevi B s ∈ DZ (gP2 hp)) :
    ((s : ℚ) = 1 ∧ (pScalar2 hp)⁻¹ * B ∈ Γ2) ∨
      ((s : ℚ) = p ∧ (∀ i j, ∃ z : ℤ, (z : ℚ) = B.val i j) ∧
        (B.val.det = p ∨ B.val.det = -p)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hxint := DZ_gP2_int hp h
  obtain ⟨hyint, hydet⟩ := (mem_DZ_gP_iff hp _).mp ((mem_DZ_gP2_iff hp _).mp h)
  have hyval : (pScalar hp * (pU v * planeLevi B s)⁻¹).val =
      (p : ℚ) • (planeLevi B⁻¹ s⁻¹ * pU (-v)).val := by
    rw [levi_plane_inv, Units.val_mul, pScalar_val, Matrix.smul_mul, Matrix.one_mul]
  rw [hyval, levi_pU_val] at hyint
  rw [det_pScalar_mul_inv, plane_det] at hydet
  rw [plane_val] at hxint
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℚ) = s := by simpa using hxint 2 2
  obtain ⟨w, hw⟩ : ∃ w : ℤ, (w : ℚ) = p * (s : ℚ)⁻¹ := by simpa using hyint 2 2
  have hs0 : (s : ℚ) ≠ 0 := Units.ne_zero s
  have hz0 : 0 < z := by exact_mod_cast hz ▸ hs
  have hzw : z * w = p := by
    have : (z : ℚ) * w = p := by rw [hz, hw]; field_simp
    exact_mod_cast this
  have hzabs : z.natAbs ∣ p := ⟨w.natAbs, by rw [← Int.natAbs_mul, hzw, Int.natAbs_natCast]⟩
  have hzn : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz0.le
  have hd0 : B.val.det * s ≠ 0 := mul_ne_zero (GL2_det_ne B) hs0
  have hdet : B.val.det * s = p ^ 2 ∨ B.val.det * s = -p ^ 2 := by
    rcases hydet with h1 | h1
    · left
      rw [mul_inv_eq_iff_eq_mul₀ hd0] at h1
      apply mul_left_cancel₀ hp0
      linear_combination -h1
    · right
      rw [mul_inv_eq_iff_eq_mul₀ hd0] at h1
      apply mul_left_cancel₀ hp0
      linear_combination h1
  rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hzabs with h1 | h1
  · -- `s = 1`
    have hs1 : (s : ℚ) = 1 := by rw [← hz, ← hzn, h1]; simp
    left
    refine ⟨hs1, ?_⟩
    rw [hs1, mul_one] at hdet
    have hC : ∀ i j : Fin 2, ∃ c : ℤ, (c : ℚ) = (p : ℚ) * (B⁻¹).val i j := by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using hyint 0 0
      · simpa using hyint 0 1
      · simpa using hyint 1 0
      · simpa using hyint 1 1
    choose C hCv using hC
    have hk : ((pScalar2 hp)⁻¹ * B)⁻¹ ∈ Γ2 := by
      apply mem_Γ2_of_int (Matrix.of C)
      · rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, pScalar2_val, Matrix.mul_smul,
          Matrix.mul_one]
        ext i j
        exact hCv i j
      · have hCdet : ((Matrix.of C).det : ℚ) = (p : ℚ) ^ 2 * (B.val.det)⁻¹ := by
          have hCm : (Matrix.of C).map (Int.cast : ℤ → ℚ) = (p : ℚ) • (B⁻¹).val := by
            ext i j; exact hCv i j
          rw [← intCast_det2, hCm, det_smul, det_inv2, Fintype.card_fin]
        have hpm : (p : ℚ) ^ 2 ≠ 0 := pow_ne_zero _ hp0
        rcases hdet with hd | hd
        · have : (Matrix.of C).det = 1 := by
            have h2 : ((Matrix.of C).det : ℚ) = 1 := by rw [hCdet, hd, mul_inv_cancel₀ hpm]
            exact_mod_cast h2
          rw [this]; rfl
        · have : (Matrix.of C).det = -1 := by
            have h2 : ((Matrix.of C).det : ℚ) = -1 := by
              rw [hCdet, hd, inv_neg, mul_neg, mul_inv_cancel₀ hpm]
            exact_mod_cast h2
          rw [this]; rfl
    simpa using Γ2.inv_mem hk
  · -- `s = p`
    have hsp : (s : ℚ) = p := by rw [← hz, ← hzn, h1]; norm_cast
    right
    refine ⟨hsp, fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using hxint 0 0
      · simpa using hxint 0 1
      · simpa using hxint 1 0
      · simpa using hxint 1 1
    · rw [hsp] at hdet
      rcases hdet with hd | hd
      · left; apply mul_right_cancel₀ hp0; linear_combination hd
      · right; apply mul_right_cancel₀ hp0; linear_combination hd

theorem levi_mk_eq (C B : GeneralLinearGroup (Fin 2) ℚ) (t s : ℚˣ) :
    (QuotientGroup.mk (C, t) : MP ⧸ ΓM0) = QuotientGroup.mk (B, s) ↔ C⁻¹ * B ∈ Γ2 ∧ s = t := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp h
    rw [Subgroup.mem_bot] at h2
    exact ⟨h1, (inv_mul_eq_one.mp h2).symm⟩
  · rintro ⟨h1, rfl⟩
    exact Subgroup.mem_prod.mpr ⟨h1, by rw [Subgroup.mem_bot]; exact inv_mul_cancel _⟩

theorem rep_plane_mem_g {g : RationalGL3} {t : HeckeCorrespondence} (ht : AwayThree t)
    (hg : t.g = g) {r : RationalGL3} (hr : r ∈ t.representatives) {v : ℚ × ℚ}
    {B : GeneralLinearGroup (Fin 2) ℚ} {s : ℚˣ} {γ : IntegralGL}
    (hdec : r = pU v * planeLevi B s * integralRational γ) :
    pU v * planeLevi B s ∈ DZ g := by
  have h1 := (repSet ht).sub r hr
  rw [hg] at h1
  have heq : pU v * planeLevi B s = r * (integralRational γ)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]; exact hdec.symm
  rw [heq]
  exact DZ_right h1 (Γ.inv_mem ⟨γ, rfl⟩)

theorem y_scalar_val (hp : p.Prime) (u : ℚ × ℚ) :
    (pScalar hp * (pU u * planeLevi (pScalar2 hp) 1)⁻¹).val =
      !![1, 0, -u.1; 0, 1, -u.2; 0, 0, (p : ℚ)] := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [levi_plane_inv, Units.val_mul, pScalar_val, Matrix.smul_mul, Matrix.one_mul, levi_pU_val,
    show ((pScalar2 hp)⁻¹).val = (p : ℚ)⁻¹ • 1 from rfl]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hp0]

/-- The radical coordinates of the class `(p·1, 1)` are exactly `ℤ²`. -/
theorem S_scalar (hp : p.Prime) (u : ℚ × ℚ) :
    pU u * planeLevi (pScalar2 hp) 1 ∈ DZ (gP2 hp) ↔ u ∈ zLat := by
  rw [mem_DZ_gP2_iff, mem_DZ_gP_iff, y_scalar_val, mem_zLat]
  have hdet : (!![1, 0, -u.1; 0, 1, -u.2; 0, 0, (p : ℚ)] : Matrix (Fin 3) (Fin 3) ℚ).det = p := by
    simp [det_fin_three]
  rw [hdet]
  constructor
  · rintro ⟨h, -⟩
    obtain ⟨z1, h1⟩ := h 0 2
    obtain ⟨z2, h2⟩ := h 1 2
    simp at h1 h2
    exact ⟨⟨-z1, by push_cast; linarith⟩, ⟨-z2, by push_cast; linarith⟩⟩
  · rintro ⟨⟨z1, h1⟩, ⟨z2, h2⟩⟩
    refine ⟨fun i j => ?_, Or.inl rfl⟩
    fin_cases i <;> fin_cases j
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨-z1, by simp [h1]⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨-z2, by simp [h2]⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨p, by simp⟩

theorem hGL_det (hp : p.Prime) (k : Fin (p + 1)) : (hGL hp k).val.det = p := by
  rw [hGL_val, intCast_det2, hnfInt_det]; norm_cast

theorem hGL_inv_val (hp : p.Prime) (k : Fin (p + 1)) :
    ((hGL hp k)⁻¹).val = (p : ℚ)⁻¹ • adjugate (hGL hp k).val := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, hGL_det, Ring.inverse_eq_inv']

theorem p_hGL_inv_int (hp : p.Prime) (k : Fin (p + 1)) (i j : Fin 2) :
    ∃ z : ℤ, (z : ℚ) = (p : ℚ) * ((hGL hp k)⁻¹).val i j := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hGL_inv_val, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul,
    adjugate_fin_two, hGL_val]
  fin_cases i <;> fin_cases j
  · exact ⟨hnfInt p k 1 1, by simp⟩
  · exact ⟨-hnfInt p k 0 1, by simp⟩
  · exact ⟨-hnfInt p k 1 0, by simp⟩
  · exact ⟨hnfInt p k 0 0, by simp⟩

/-- For a Hermite class `(H, p)` the radical coordinates lie in the conjugation lattice. -/
theorem S_hermite_le (hp : p.Prime) (k : Fin (p + 1)) (u : ℚ × ℚ)
    (h : pU u * planeLevi (hGL hp k) (pUnit hp) ∈ DZ (gP2 hp)) :
    u ∈ planeData.latt (hGL hp k, pUnit hp) := by
  obtain ⟨hyint, -⟩ := (mem_DZ_gP_iff hp _).mp ((mem_DZ_gP2_iff hp _).mp h)
  rw [levi_plane_inv, Units.val_mul, pScalar_val, Matrix.smul_mul, Matrix.one_mul,
    levi_pU_val] at hyint
  obtain ⟨z1, h1⟩ := hyint 0 2
  obtain ⟨z2, h2⟩ := hyint 1 2
  simp at h1 h2
  rw [ParabolicData.latt, AddSubgroup.mem_comap, mem_zLat]
  simp only [planeData, matHom_apply, pUnit_val, Matrix.smul_apply, smul_eq_mul]
  exact ⟨⟨-z1, by push_cast; linear_combination -h1⟩, ⟨-z2, by push_cast; linear_combination -h2⟩⟩

theorem S_hermite_zero (hp : p.Prime) (k : Fin (p + 1)) :
    pU 0 * planeLevi (hGL hp k) (pUnit hp) ∈ DZ (gP2 hp) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [mem_DZ_gP2_iff, mem_DZ_gP_iff, det_pScalar_mul_inv, plane_det, hGL_det, pUnit_val]
  refine ⟨fun i j => ?_, Or.inl (by field_simp)⟩
  rw [levi_plane_inv, Units.val_mul, pScalar_val, Matrix.smul_mul, Matrix.one_mul, levi_pU_val]
  fin_cases i <;> fin_cases j
  · simpa using p_hGL_inv_int hp k 0 0
  · simpa using p_hGL_inv_int hp k 0 1
  · exact ⟨0, by simp⟩
  · simpa using p_hGL_inv_int hp k 1 0
  · simpa using p_hGL_inv_int hp k 1 1
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp [pUnit_val, hp0]⟩

/-- **The plane eigenvalue of `diag(p,p,1)`.** Every correspondence of this double coset has
`p² + p + 1` representatives and plane eigenvalue `p² W(p·1, 1) + (p + 1) W(diag(p,1), p)`. -/
theorem prime2_plane_eigenvalue (D : InducingData n) (hp : p.Prime) (t : HeckeCorrespondence)
    (ht : AwayThree t) (hg : t.g = gP2 hp) :
    t.representatives.card = p ^ 2 + p + 1 ∧
      ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
        ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
          ((p : ℂ) ^ 2 * ratPlaneWeight D (pScalar2 hp) 1 +
            ((p : ℂ) + 1) * ratPlaneWeight D (dP hp) (pUnit hp)) * f g := by
  classical
  choose vP BP sP γP hsP hP using plane_iwasawa_pos
  have hform := plane_rational_formula D t ht vP BP sP γP (fun r _ => hP r)
  have hRS := repSet ht
  have hDl : ∀ γ ∈ Γ, ∀ x ∈ DZ t.g, γ * x ∈ DZ t.g := fun γ hγ x hx => DZ_left hx hγ
  have hDr : ∀ x ∈ DZ t.g, ∀ γ ∈ Γ, x * γ ∈ DZ t.g := fun x hx γ hγ => DZ_right hx hγ
  have hdecP : ∀ r ∈ t.representatives, 0 < (((BP r, sP r) : MP).2 : ℚ) ∧
      r⁻¹ * (planeData.U (vP r) * planeData.L (BP r, sP r)) ∈ Γ := by
    intro r _
    refine ⟨hsP r, ?_⟩
    change r⁻¹ * (pU (vP r) * planeLevi (BP r) (sP r)) ∈ Γ
    have : pU (vP r) * planeLevi (BP r) (sP r) = r * (integralRational (γP r))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact (hP r).symm
    rw [this, inv_mul_cancel_left]
    exact Γ.inv_mem ⟨_, rfl⟩
  have hlevi : ∀ r ∈ t.representatives, _ := fun r hr =>
    prime2_plane_levi hp _ _ _ (hsP r) (rep_plane_mem_g ht hg hr (hP r))
  have hp1 : ((p : ℚ)) ≠ 1 := by exact_mod_cast hp.one_lt.ne'
  let cls : RationalGL3 → MP ⧸ ΓM0 := fun r => QuotientGroup.mk (BP r, sP r)
  -- weights
  have hterm : ∀ r ∈ t.representatives, ratPlaneWeight D (BP r) (sP r) =
      if (sP r : ℚ) = 1 then ratPlaneWeight D (pScalar2 hp) 1
      else ratPlaneWeight D (dP hp) (pUnit hp) := by
    intro r hr
    rcases hlevi r hr with ⟨hs, hk⟩ | ⟨hs, hB, hdet⟩
    · rw [ite_eq_left hs, show sP r = 1 from Units.ext (by rw [hs, Units.val_one]),
        show BP r = pScalar2 hp * ((pScalar2 hp)⁻¹ * BP r) by group, ratPlaneWeight_mul D _ _ hk]
    · have hne : ¬ (sP r : ℚ) = 1 := by rw [hs]; exact hp1
      rw [ite_eq_right hne, weight_int_det D hp _ hB hdet,
        show sP r = pUnit hp from Units.ext (by rw [hs, pUnit_val])]
  -- the class `(p·1, 1)`
  have hcount1 : (t.representatives.filter (fun r => (sP r : ℚ) = 1)).card = p ^ 2 := by
    have hfilter : t.representatives.filter (fun r => (sP r : ℚ) = 1) =
        t.representatives.filter (fun r => cls r =
          QuotientGroup.mk (pScalar2 hp, (1 : ℚˣ))) := by
      refine Finset.filter_congr fun r hr => ?_
      constructor
      · intro hs
        rcases hlevi r hr with ⟨_, hk⟩ | ⟨hs', -, -⟩
        · exact ((levi_mk_eq _ _ _ _).mpr ⟨hk, Units.ext (by rw [hs, Units.val_one])⟩).symm
        · exact absurd (hs.symm.trans hs') (Ne.symm hp1)
      · intro h
        have := ((levi_mk_eq _ _ _ _).mp h.symm).2
        rw [this, Units.val_one]
    rw [hfilter, planeData.fiber_card hRS ΓM0 ΓM0_le (fun m : MP => 0 < (m.2 : ℚ)) pos_class
      vP (fun r => (BP r, sP r)) hdecP (pScalar2 hp, (1 : ℚˣ)) (by simp)]
    have hC := plane_count hDl hDr (pScalar2 hp) 1
    have hdet1 : |(((1 : ℚˣ)⁻¹ : ℚˣ).val • (pScalar2 hp).val).det| = (p : ℚ) ^ 2 := by
      rw [inv_one, Units.val_one, one_smul, pScalar2_val, det_smul, det_one, Fintype.card_fin,
        mul_one]
      exact abs_of_nonneg (by positivity)
    have hS : planeData.S (DZ t.g) (pScalar2 hp, (1 : ℚˣ)) = (zLat : Set (ℚ × ℚ)) := by
      ext u
      change pU u * planeLevi (pScalar2 hp) 1 ∈ DZ t.g ↔ u ∈ zLat
      rw [hg, S_scalar]
    have hNL : planeData.NL (DZ t.g) (pScalar2 hp, (1 : ℚˣ)) = 1 := by
      rw [ParabolicData.NL, hS, Set.ncard_eq_one]
      refine ⟨0, Set.ext fun y => ?_⟩
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [Set.mem_singleton_iff, QuotientAddGroup.eq_zero_iff]
        exact hu
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        exact ⟨0, zLat.zero_mem, by rw [hy]; rfl⟩
    rw [hdet1, hNL, Nat.cast_one, mul_one] at hC
    exact_mod_cast hC
  -- the Hermite classes `(H, p)`
  have hcountp : (t.representatives.filter (fun r => ¬ (sP r : ℚ) = 1)).card = p + 1 := by
    let H : Fin (p + 1) → MP ⧸ ΓM0 := fun k => QuotientGroup.mk (hGL hp k, pUnit hp)
    have hHinj : Function.Injective H := by
      intro i j hij
      exact hGL_inj hp ((levi_mk_eq _ _ _ _).mp hij).1
    have hmaps : Set.MapsTo cls ↑(t.representatives.filter (fun r => ¬ (sP r : ℚ) = 1))
        ↑(Finset.univ.image H) := by
      intro r hr
      rw [Finset.coe_filter] at hr
      obtain ⟨hr, hne⟩ := hr
      rcases hlevi r hr with ⟨hs, -⟩ | ⟨hs, hB, hdet⟩
      · exact absurd hs hne
      obtain ⟨k, hk⟩ := hGL_class hp (BP r) hB hdet
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ⟨k, (levi_mk_eq _ _ _ _).mpr ⟨hk, Units.ext (by rw [hs, pUnit_val])⟩⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_image (fun i _ j _ h => hHinj h)]
    have hfib : ∀ k : Fin (p + 1),
        ((t.representatives.filter (fun r => ¬ (sP r : ℚ) = 1)).filter
          (fun r => cls r = H k)).card = 1 := by
      intro k
      have hfilt : (t.representatives.filter (fun r => ¬ (sP r : ℚ) = 1)).filter
          (fun r => cls r = H k) = t.representatives.filter
            (fun r => (QuotientGroup.mk (BP r, sP r) : MP ⧸ ΓM0) =
              QuotientGroup.mk (hGL hp k, pUnit hp)) := by
        rw [Finset.filter_filter]
        refine Finset.filter_congr fun r _ => ?_
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨?_, h⟩
          have := ((levi_mk_eq _ _ _ _).mp h.symm).2
          rw [this, pUnit_val]
          exact hp1
      rw [hfilt, planeData.fiber_card hRS ΓM0 ΓM0_le (fun m : MP => 0 < (m.2 : ℚ)) pos_class
        vP (fun r => (BP r, sP r)) hdecP (hGL hp k, pUnit hp)
        (by rw [pUnit_val]; exact_mod_cast hp.pos)]
      rw [Set.ncard_eq_one]
      refine ⟨0, Set.ext fun y => ?_⟩
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [Set.mem_singleton_iff, QuotientAddGroup.eq_zero_iff]
        have hu' : pU u * planeLevi (hGL hp k) (pUnit hp) ∈ DZ (gP2 hp) := by
          rw [← hg]; exact hu
        exact S_hermite_le hp k u hu'
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        refine ⟨0, ?_, by rw [hy]; rfl⟩
        change pU 0 * planeLevi (hGL hp k) (pUnit hp) ∈ DZ t.g
        rw [hg]; exact S_hermite_zero hp k
    rw [Finset.sum_congr rfl (fun k _ => hfib k), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  refine ⟨?_, fun f hf g => ?_⟩
  · rw [← Finset.card_filter_add_card_filter_not (fun r => (sP r : ℚ) = 1), hcount1, hcountp]
    ring
  rw [hform f hf g, Finset.sum_congr rfl hterm, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, hcount1, hcountp]
  push_cast
  ring

/-- The plane weight factors through the two Levi components. -/
theorem ratPlaneWeight_split (D : InducingData n) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) :
    ratPlaneWeight D B s * ratPlaneWeight D 1 1 = ratPlaneWeight D B 1 * ratPlaneWeight D 1 s := by
  simp only [ratPlaneWeight, planeWeight]
  ring

/-- **The `diag(p,p,1)` eigenvalue in split form.** -/
theorem prime2_plane_eigenvalue_split (D : InducingData n) (hp : p.Prime) (t : HeckeCorrespondence)
    (ht : AwayThree t) (hg : t.g = gP2 hp) :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      (∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r))) * ratPlaneWeight D 1 1 =
        ((p : ℂ) ^ 2 * ratPlaneWeight D (pScalar2 hp) 1 * ratPlaneWeight D 1 1 +
          ((p : ℂ) + 1) * ratPlaneWeight D (dP hp) 1 * ratPlaneWeight D 1 (pUnit hp)) * f g := by
  intro f hf g
  rw [(prime2_plane_eigenvalue D hp t ht hg).2 f hf g]
  have := ratPlaneWeight_split D (dP hp) (pUnit hp)
  linear_combination ((p : ℂ) + 1) * f g * this

end TernaryPeriodPolynomials.HeckeEigen.Satake
