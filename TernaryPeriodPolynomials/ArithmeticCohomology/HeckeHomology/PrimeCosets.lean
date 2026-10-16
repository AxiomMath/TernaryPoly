module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Mackey
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Prime
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.PHLevi

@[expose] public section


/-!
# Prime Hecke datum: the double cosets `S_p \ GL₃(ℤ) / P_H` and the two `P_H`-level correspondences

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryHeckeCosets TernaryPeriodPolynomials.Argument.AppendixBResidue

variable (p : ℕ) [Fact p.Prime]

/-- `S_p = {k | p ∣ k₀₁, p ∣ k₀₂}`. -/
abbrev Sp : Subgroup IntegralGL := commSubgroup OrdinaryFullAction.integral (gInv p)

theorem mem_Sp (k : IntegralGL) : k ∈ Sp p ↔ (p : ℤ) ∣ k.val 0 1 ∧ (p : ℤ) ∣ k.val 0 2 :=
  mem_commSubgroup_gInv p k

instance primeDatum_finiteIndex : (primeDatum p).S.FiniteIndex := (primeDatum p).finiteIndex

theorem PH_le_Sp : PH ≤ Sp p := by
  intro k hk
  rw [mem_Sp]
  obtain ⟨h1, h2⟩ := (mem_PH_iff_row k).mp hk
  rw [h1, h2]
  exact ⟨dvd_zero _, dvd_zero _⟩

/-- The transposition `(0 1)` as an element of `GL₃(ℤ)`. -/
def sigma : IntegralGL :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem sigma_val : sigma.val = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := rfl

theorem sigma_mul_sigma : sigma * sigma = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma, Matrix.mul_apply, Fin.sum_univ_three]

theorem sigma_inv : sigma⁻¹ = sigma := inv_eq_of_mul_eq_one_right sigma_mul_sigma


section Entries

variable {p}

theorem f_matrix (s : ↥(primeDatum p).S) :
    (OrdinaryFullAction.integral ((primeDatum p).f s)).val =
      !![((s.1.val 0 0 : ℤ) : ℚ), (s.1.val 0 1 : ℚ) / p, (s.1.val 0 2 : ℚ) / p;
        p * (s.1.val 1 0 : ℚ), (s.1.val 1 1 : ℚ), (s.1.val 1 2 : ℚ);
        p * (s.1.val 2 0 : ℚ), (s.1.val 2 1 : ℚ), (s.1.val 2 2 : ℚ)] := by
  have h := (primeDatum p).hf s
  have hg : (gInv p)⁻¹ = primeDiagonal p := by unfold gInv; exact inv_inv _
  rw [hg] at h
  rw [h]
  exact primeDiagonal_conjugate p s.1

theorem f_ent (s : ↥(primeDatum p).S) (i j : Fin 3) :
    ((((primeDatum p).f s : IntegralGL).val i j : ℤ) : ℚ) =
      (!![((s.1.val 0 0 : ℤ) : ℚ), (s.1.val 0 1 : ℚ) / p, (s.1.val 0 2 : ℚ) / p;
        p * (s.1.val 1 0 : ℚ), (s.1.val 1 1 : ℚ), (s.1.val 1 2 : ℚ);
        p * (s.1.val 2 0 : ℚ), (s.1.val 2 1 : ℚ), (s.1.val 2 2 : ℚ)] : Matrix (Fin 3) (Fin 3) ℚ) i j := by
  rw [← f_matrix]
  rfl

theorem f_val_01 (s : ↥(primeDatum p).S) : ((primeDatum p).f s : IntegralGL).val 0 1 * p = s.1.val 0 1 := by
  have h := f_ent s 0 1
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simp at h
  have : (((primeDatum p).f s : IntegralGL).val 0 1 : ℚ) * p = (s.1.val 0 1 : ℚ) := by
    rw [h]; field_simp
  exact_mod_cast this

theorem f_val_02 (s : ↥(primeDatum p).S) : ((primeDatum p).f s : IntegralGL).val 0 2 * p = s.1.val 0 2 := by
  have h := f_ent s 0 2
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simp at h
  have : (((primeDatum p).f s : IntegralGL).val 0 2 : ℚ) * p = (s.1.val 0 2 : ℚ) := by
    rw [h]; field_simp
  exact_mod_cast this

theorem f_val_00 (s : ↥(primeDatum p).S) : ((primeDatum p).f s : IntegralGL).val 0 0 = s.1.val 0 0 := by
  have h := f_ent s 0 0
  simp at h
  exact_mod_cast h

theorem f_val_10 (s : ↥(primeDatum p).S) : ((primeDatum p).f s : IntegralGL).val 1 0 = p * s.1.val 1 0 := by
  have h := f_ent s 1 0
  simp at h
  exact_mod_cast h

theorem f_val_11 (s : ↥(primeDatum p).S) : ((primeDatum p).f s : IntegralGL).val 1 1 = s.1.val 1 1 := by
  have h := f_ent s 1 1
  simp at h
  exact_mod_cast h

theorem f_val_12 (s : ↥(primeDatum p).S) : ((primeDatum p).f s : IntegralGL).val 1 2 = s.1.val 1 2 := by
  have h := f_ent s 1 2
  simp at h
  exact_mod_cast h

theorem f_val_20 (s : ↥(primeDatum p).S) : ((primeDatum p).f s : IntegralGL).val 2 0 = p * s.1.val 2 0 := by
  have h := f_ent s 2 0
  simp at h
  exact_mod_cast h

theorem f_val_21 (s : ↥(primeDatum p).S) : ((primeDatum p).f s : IntegralGL).val 2 1 = s.1.val 2 1 := by
  have h := f_ent s 2 1
  simp at h
  exact_mod_cast h

theorem f_val_22 (s : ↥(primeDatum p).S) : ((primeDatum p).f s : IntegralGL).val 2 2 = s.1.val 2 2 := by
  have h := f_ent s 2 2
  simp at h
  exact_mod_cast h

end Entries


section Homs

variable {p}

theorem sigma_conj_val (k : IntegralGL) :
    (sigma * k * sigma).val = !![k.val 1 1, k.val 1 0, k.val 1 2; k.val 0 1, k.val 0 0, k.val 0 2;
      k.val 2 1, k.val 2 0, k.val 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem sigma_conj_inv (k : IntegralGL) : sigma⁻¹ * k * sigma = sigma * k * sigma := by
  rw [sigma_inv]

theorem p_ne_zero_int : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- `f₃ : P_H → P_H`, `(η, u, D) ↦ (η, p u, D)`: the Hecke map `g (·) g⁻¹` restricted to `P_H ⊂ S_p`. -/
def f3 (p : ℕ) [Fact p.Prime] : PH →* PH :=
  (((primeDatum p).f.comp (Subgroup.inclusion (PH_le_Sp p : PH ≤ (primeDatum p).S))).codRestrict PH
    (fun h => by
      obtain ⟨h1, h2⟩ := (mem_PH_iff_row h.1).mp h.2
      refine (mem_PH_iff_row _).mpr ⟨?_, ?_⟩
      · have := f_val_01 (p := p) ⟨h.1, PH_le_Sp p h.2⟩
        have h1' : (h.1.val 0 1) = 0 := h1
        rw [h1'] at this
        exact (mul_eq_zero.mp this).resolve_right p_ne_zero_int
      · have := f_val_02 (p := p) ⟨h.1, PH_le_Sp p h.2⟩
        have h2' : (h.1.val 0 2) = 0 := h2
        rw [h2'] at this
        exact (mul_eq_zero.mp this).resolve_right p_ne_zero_int))

theorem f3_coe (h : PH) : ((f3 p h : PH) : IntegralGL) =
    (primeDatum p).f (Subgroup.inclusion (PH_le_Sp p : PH ≤ (primeDatum p).S) h) := rfl

/-- `f₁ : P_H ∩ σ⁻¹ S_p σ → P_H`, `h ↦ σ⁻¹ f(σ h σ⁻¹) σ`. -/
def f1 : ↥(Sx PH (primeDatum p).S sigma) →* PH :=
  (((MulAut.conj sigma⁻¹).toMonoidHom).comp ((primeDatum p).f.comp (mX PH (primeDatum p).S sigma))).codRestrict PH
    (fun h => by
      obtain ⟨h1, h2⟩ := (mem_PH_iff_row (h.1.1 : IntegralGL)).mp h.1.2
      have hs : ((mX PH (primeDatum p).S sigma h : ↥(primeDatum p).S) : IntegralGL) =
          sigma * h.1.1 * sigma⁻¹ := rfl
      have hsv : ((mX PH (primeDatum p).S sigma h : ↥(primeDatum p).S) : IntegralGL).val =
          (sigma * h.1.1 * sigma).val := by
        rw [hs, sigma_inv]
      have e10 : ((mX PH (primeDatum p).S sigma h : ↥(primeDatum p).S) : IntegralGL).val 1 0 = 0 := by
        rw [hsv, sigma_conj_val]; simpa using h1
      have e12 : ((mX PH (primeDatum p).S sigma h : ↥(primeDatum p).S) : IntegralGL).val 1 2 = 0 := by
        rw [hsv, sigma_conj_val]; simpa using h2
      refine (mem_PH_iff_row _).mpr ⟨?_, ?_⟩
      · change (sigma⁻¹ * ((primeDatum p).f (mX PH (primeDatum p).S sigma h) : IntegralGL) * sigma⁻¹⁻¹).val 0 1 = 0
        rw [inv_inv, sigma_inv, sigma_conj_val]
        simp [f_val_10, e10]
      · change (sigma⁻¹ * ((primeDatum p).f (mX PH (primeDatum p).S sigma h) : IntegralGL) * sigma⁻¹⁻¹).val 0 2 = 0
        rw [inv_inv, sigma_inv, sigma_conj_val]
        simp [f_val_12, e12])

end Homs


section Cosets

variable {p}

theorem mem_Sx_sigma_iff (h : PH) :
    h ∈ Sx PH (primeDatum p).S sigma ↔ (p : ℤ) ∣ h.1.val 1 0 ∧ (p : ℤ) ∣ h.1.val 1 2 := by
  rw [mem_Sx]
  change sigma * h.1 * sigma⁻¹ ∈ Sp p ↔ _
  rw [mem_Sp, sigma_inv, sigma_conj_val]
  simp

theorem one_mem_Sx (h : PH) : h ∈ Sx PH (primeDatum p).S 1 := by
  rw [mem_Sx]
  change (1 : IntegralGL) * h.1 * (1 : IntegralGL)⁻¹ ∈ Sp p
  simpa using PH_le_Sp p h.2

theorem det_PH_dvd (k : IntegralGL) (hk : k ∈ PH) (hd : (p : ℤ) ∣ k.val 1 1 ∧ (p : ℤ) ∣ k.val 1 2) : False := by
  obtain ⟨h1, h2⟩ := (mem_PH_iff_row k).mp hk
  have hu : IsUnit k.val.det := (Matrix.isUnit_iff_isUnit_det _).mp k.isUnit
  have hdet : k.val.det = k.val 0 0 * (k.val 1 1 * k.val 2 2 - k.val 1 2 * k.val 2 1) := by
    rw [Matrix.det_fin_three, h1, h2]; ring
  have hdvd : (p : ℤ) ∣ k.val.det := by
    rw [hdet]
    exact Dvd.dvd.mul_left (dvd_sub (Dvd.dvd.mul_right hd.1 _) (Dvd.dvd.mul_right hd.2 _)) _
  have hp : IsUnit (p : ℤ) := isUnit_of_dvd_unit hdvd hu
  have := Int.isUnit_iff.mp hp
  have hp1 : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  omega

theorem sigma_mul_PH_not_mem (k : IntegralGL) (hk : k ∈ PH) : sigma * k ∉ Sp p := by
  intro h
  rw [mem_Sp] at h
  have e : ∀ j, (sigma * k).val 0 j = k.val 1 j := fun j => by
    fin_cases j <;> simp [sigma, Matrix.mul_apply, Fin.sum_univ_three]
  rw [e 1, e 2] at h
  exact det_PH_dvd k hk h

end Cosets


section Cover

/-- The element `(1 0 0; u D)` of `P_H` (for `det D = 1`). -/
def mkPH (u0 u1 d00 d01 d10 d11 : ℤ) (hdet : d00 * d11 - d01 * d10 = 1) : IntegralGL :=
  ⟨!![1, 0, 0; u0, d00, d01; u1, d10, d11],
    !![1, 0, 0; -(d11 * u0 - d01 * u1), d11, -d01; -(-d10 * u0 + d00 * u1), -d10, d00],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | ring1 | linear_combination hdet | linear_combination (-u0) * hdet |
          linear_combination (-u1) * hdet,
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | ring1 | linear_combination hdet⟩

theorem mkPH_val (u0 u1 d00 d01 d10 d11 : ℤ) (hdet : d00 * d11 - d01 * d10 = 1) :
    (mkPH u0 u1 d00 d01 d10 d11 hdet).val = !![1, 0, 0; u0, d00, d01; u1, d10, d11] := rfl

theorem mkPH_mem (u0 u1 d00 d01 d10 d11 : ℤ) (hdet : d00 * d11 - d01 * d10 = 1) :
    mkPH u0 u1 d00 d01 d10 d11 hdet ∈ PH := by
  rw [mem_PH_iff_row, mkPH_val]
  simp

end Cover


section Cover2

variable {p}

theorem dvd_of_zmod_eq (n : ℤ) (h : ((n : ℤ) : ZMod p) = 0) : (p : ℤ) ∣ n :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp h

theorem exists_PH_row (a b c : ℤ) (hbc : ¬ ((p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)) :
    ∃ h ∈ PH, (p : ℤ) ∣ (a * h.val 0 0 + b * h.val 1 0 + c * h.val 2 0) ∧
      (p : ℤ) ∣ (b * h.val 1 2 + c * h.val 2 2) := by
  by_cases hc : (p : ℤ) ∣ c
  · have hb : ¬ (p : ℤ) ∣ b := fun hb => hbc ⟨hb, hc⟩
    have hb0 : ((b : ℤ) : ZMod p) ≠ 0 := fun h => hb (dvd_of_zmod_eq b h)
    refine ⟨mkPH ((-(a : ZMod p) * (b : ZMod p)⁻¹).val : ℤ) 0 1 0 0 1 (by norm_num), mkPH_mem _ _ _ _ _ _ _, ?_, ?_⟩
    · rw [mkPH_val]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      apply dvd_of_zmod_eq
      push_cast
      simp
      have : (b : ZMod p) * ((a : ZMod p) * (b : ZMod p)⁻¹) = a := by field_simp
      rw [this]; ring
    · rw [mkPH_val]
      simp
      exact hc
  · have hc0 : ((c : ℤ) : ZMod p) ≠ 0 := fun h => hc (dvd_of_zmod_eq c h)
    refine ⟨mkPH 0 ((-(a : ZMod p) * (c : ZMod p)⁻¹).val : ℤ) 0 1 (-1) (((-(b : ZMod p) * (c : ZMod p)⁻¹).val : ℕ) : ℤ)
      (by ring), mkPH_mem _ _ _ _ _ _ _, ?_, ?_⟩
    · rw [mkPH_val]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      apply dvd_of_zmod_eq
      push_cast
      simp
      have : (c : ZMod p) * ((a : ZMod p) * (c : ZMod p)⁻¹) = a := by field_simp
      rw [this]; ring
    · rw [mkPH_val]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      apply dvd_of_zmod_eq
      push_cast
      simp
      have : (c : ZMod p) * ((b : ZMod p) * (c : ZMod p)⁻¹) = b := by field_simp
      rw [this]; ring

end Cover2


section Reps

open scoped Classical

/-- `{1, σ}` is a complete set of representatives of `S_p \ GL₃(ℤ) / P_H`. -/
theorem doubleCosetReps : DoubleCosetReps PH (primeDatum p).S ({1, sigma} : Finset IntegralGL) where
  cover y := by
    by_cases hy : (p : ℤ) ∣ y.val 0 1 ∧ (p : ℤ) ∣ y.val 0 2
    · refine ⟨1, by simp, y, (mem_Sp p y).mpr hy, 1, PH.one_mem, by simp⟩
    · obtain ⟨h, hh, h1, h2⟩ := exists_PH_row (p := p) (y.val 0 0) (y.val 0 1) (y.val 0 2) hy
      refine ⟨sigma, by simp, y * h * sigma, ?_, h⁻¹, PH.inv_mem hh, ?_⟩
      · rw [show (primeDatum p).S = Sp p from rfl, mem_Sp]
        have h02 : h.val 0 2 = 0 := ((mem_PH_iff_row h).mp hh).2
        have e01 : (y * h * sigma).val 0 1 =
            y.val 0 0 * h.val 0 0 + y.val 0 1 * h.val 1 0 + y.val 0 2 * h.val 2 0 := by
          simp [sigma, Matrix.mul_apply, Fin.sum_univ_three]
        have e02 : (y * h * sigma).val 0 2 = y.val 0 1 * h.val 1 2 + y.val 0 2 * h.val 2 2 := by
          simp [sigma, Matrix.mul_apply, Fin.sum_univ_three, h02]
        rw [e01, e02]
        exact ⟨h1, h2⟩
      · calc y = y * h * (sigma * sigma) * h⁻¹ := by rw [sigma_mul_sigma]; group
          _ = y * h * sigma * sigma * h⁻¹ := by group
  disjoint := by
    intro x hx x' hx' s hs s' hs' h hh h' hh' heq
    have hs1 : s ∈ Sp p := hs
    have hs1' : s' ∈ Sp p := hs'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · rfl
    · exfalso
      have key : sigma * (h' * h⁻¹) = s'⁻¹ * s := by
        have : s' * sigma * h' = s * h := by simpa using heq.symm
        calc sigma * (h' * h⁻¹) = s'⁻¹ * (s' * sigma * h') * h⁻¹ := by group
          _ = s'⁻¹ * (s * h) * h⁻¹ := by rw [this]
          _ = s'⁻¹ * s := by group
      exact sigma_mul_PH_not_mem (p := p) (h' * h⁻¹) (PH.mul_mem hh' (PH.inv_mem hh))
        (key ▸ (Sp p).mul_mem ((Sp p).inv_mem hs1') hs1)
    · exfalso
      have key : sigma * (h * h'⁻¹) = s⁻¹ * s' := by
        have : s * sigma * h = s' * h' := by simpa using heq
        calc sigma * (h * h'⁻¹) = s⁻¹ * (s * sigma * h) * h'⁻¹ := by group
          _ = s⁻¹ * (s' * h') * h'⁻¹ := by rw [this]
          _ = s⁻¹ * s' := by group
      exact sigma_mul_PH_not_mem (p := p) (h * h'⁻¹) (PH.mul_mem hh (PH.inv_mem hh'))
        (key ▸ (Sp p).mul_mem ((Sp p).inv_mem hs1) hs1')
    · rfl

end Reps


section Data

variable {p}

/-- `ξ₁ = σ⁻¹ g σ = diag(1, 1/p, 1)`. -/
def xi1 (p : ℕ) [Fact p.Prime] : OrdinaryFullAction.GL3 := (OrdinaryFullAction.integral sigma)⁻¹ * gInv p * OrdinaryFullAction.integral sigma

theorem gInv_mul_sigma :
    gInv p * OrdinaryFullAction.integral sigma = OrdinaryFullAction.integral sigma * xi1 p := by
  unfold xi1; group

theorem gInv_mul_one :
    gInv p * OrdinaryFullAction.integral (1 : IntegralGL) = OrdinaryFullAction.integral (1 : IntegralGL) * gInv p := by
  simp

theorem f3_hf (h : PH) :
    OrdinaryFullAction.integral ((f3 p h : PH) : IntegralGL) =
      gInv p * OrdinaryFullAction.integral (h : IntegralGL) * (gInv p)⁻¹ :=
  (primeDatum p).hf (Subgroup.inclusion (PH_le_Sp p : PH ≤ (primeDatum p).S) h)

/-- `f₀ : P_H ∩ 1⁻¹ S 1 → P_H`, the restriction of `f₃`. -/
def f0 (p : ℕ) [Fact p.Prime] : ↥(Sx PH (primeDatum p).S 1) →* PH := (f3 p).comp (Sx PH (primeDatum p).S 1).subtype

theorem f0_hf (h : ↥(Sx PH (primeDatum p).S 1)) :
    OrdinaryFullAction.integral (((f0 p h : PH)) : IntegralGL) =
      gInv p * OrdinaryFullAction.integral (((h : PH)) : IntegralGL) * (gInv p)⁻¹ :=
  f3_hf (h : PH)

theorem f1_hf (h : ↥(Sx PH (primeDatum p).S sigma)) :
    OrdinaryFullAction.integral ((f1 (p := p) h : PH) : IntegralGL) =
      xi1 p * OrdinaryFullAction.integral (((h : PH)) : IntegralGL) * (xi1 p)⁻¹ := by
  have h1 := (primeDatum p).hf (mX PH (primeDatum p).S sigma h)
  have e : ((f1 (p := p) h : PH) : IntegralGL) =
      sigma⁻¹ * ((primeDatum p).f (mX PH (primeDatum p).S sigma h) : IntegralGL) * sigma⁻¹⁻¹ := rfl
  rw [e, map_mul, map_mul, h1, mX_coe]
  unfold xi1
  simp only [map_mul, map_inv]
  group

end Data

end TernaryPeriodPolynomials.Argument.HeckeHomology
