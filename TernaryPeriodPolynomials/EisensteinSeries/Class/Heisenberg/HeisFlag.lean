module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Instance
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisForm1

@[expose] public section


open scoped ContDiff MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

open TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- **The stabilizer in `SL₃(ℤ)` of the standard complete flag**: the upper triangular matrices. -/
def borelStab : Subgroup SL(3, ℤ) where
  carrier := {γ | (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧ (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
    (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0}
  mul_mem' := by
    rintro γ δ ⟨h0, h1, h2⟩ ⟨k0, k1, k2⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, k0, k1, k2]
  one_mem' := by simp
  inv_mem' := by
    rintro γ ⟨h0, h1, h2⟩
    show (_ : Prop)
    simp only [Set.mem_ofPred_eq]
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, h0, h1, h2]

/-- **The flag group `Γ_B = Γ(N) ∩ B(ℤ)`** ("at a flag use two normal coordinates"). -/
def flagGroup (N : ℕ) : Subgroup SL(3, ℤ) := gammaN N ⊓ borelStab

section Entries

variable {N : ℕ}

theorem diag_eq_one {d : ℤ} (hd : d = 1 ∨ d = -1) (h : (N : ℤ) ∣ d - 1) (hN : 3 ≤ N) : d = 1 := by
  rcases hd with hd | hd
  · exact hd
  · exfalso
    rw [hd] at h
    have h2 : (N : ℤ) ∣ 2 := by
      have := dvd_neg.mpr h
      simpa using this
    have := Int.le_of_dvd (by norm_num) h2
    omega

/-- **The entries of an element of `Γ_B`**: unipotent upper triangular with the three entries divisible by `N` (`N ≥ 3`). -/
theorem flag_entries (hN : 3 ≤ N) {γ : SL(3, ℤ)} (hγ : γ ∈ flagGroup N) :
    (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧ (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 1 = 1 ∧
      (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 ∧ (N : ℤ) ∣ (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 ∧
      (N : ℤ) ∣ (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 ∧ (N : ℤ) ∣ (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 2 := by
  obtain ⟨hg, h10, h20, h21⟩ := hγ
  have hm := mem_gammaN.1 hg
  have hdet : (γ : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_three, h10, h20, h21] at hdet
  have hprod : (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * ((γ : Matrix (Fin 3) (Fin 3) ℤ) 1 1 *
      (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2) = 1 := by linear_combination hdet
  have u0 := Int.eq_one_or_neg_one_of_mul_eq_one hprod
  have hprod1 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * ((γ : Matrix (Fin 3) (Fin 3) ℤ) 0 0 *
      (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2) = 1 := by linear_combination hdet
  have u1 := Int.eq_one_or_neg_one_of_mul_eq_one hprod1
  have hprod2 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * ((γ : Matrix (Fin 3) (Fin 3) ℤ) 0 0 *
      (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 1) = 1 := by linear_combination hdet
  have u2 := Int.eq_one_or_neg_one_of_mul_eq_one hprod2
  refine ⟨diag_eq_one u0 (by simpa using hm 0 0) hN, diag_eq_one u1 (by simpa using hm 1 1) hN,
    diag_eq_one u2 (by simpa using hm 2 2) hN, by simpa using hm 0 1, by simpa using hm 1 2,
    by simpa using hm 0 2⟩

end Entries

section FlagLattice

variable {N : ℕ}

/-- **The Malcev coordinates `(x, y, z) = (γ₀₁, γ₁₂, γ₀₂)` of an element of `Γ_B`.** -/
def flagN (γ : SL(3, ℤ)) : Pt :=
  (((γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 : ℤ), ((γ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 : ℤ),
    ((γ : Matrix (Fin 3) (Fin 3) ℤ) 0 2 : ℤ))

theorem flagN_mul (hN : 3 ≤ N) {γ δ : SL(3, ℤ)} (hγ : γ ∈ flagGroup N) (hδ : δ ∈ flagGroup N) :
    flagN (γ * δ) = mulH (flagN γ) (flagN δ) := by
  obtain ⟨g00, g11, g22, -⟩ := flag_entries hN hγ
  obtain ⟨d00, d11, d22, -⟩ := flag_entries hN hδ
  obtain ⟨-, g10, g20, g21⟩ := hγ
  obtain ⟨-, d10, d20, d21⟩ := hδ
  simp only [flagN, mulH]
  ext
  · simp [Matrix.mul_apply, Fin.sum_univ_three, g00, d11, d21]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_three, g11, d22, g10]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_three, g00, d22]
    ring

end FlagLattice

section Gens

variable {N : ℕ}

/-- **The unipotent upper triangular matrix** `[[1, a, c], [0, 1, b], [0, 0, 1]]` of `SL₃(ℤ)`. -/
def unipMat (a b c : ℤ) : SL(3, ℤ) :=
  ⟨!![1, a, c; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem unipMat_mem {a b c : ℤ} (ha : (N : ℤ) ∣ a) (hb : (N : ℤ) ∣ b) (hc : (N : ℤ) ∣ c) :
    unipMat a b c ∈ flagGroup N := by
  rw [flagGroup, Subgroup.mem_inf]
  refine ⟨mem_gammaN.2 fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [unipMat, ha, hb, hc]
  · show (unipMat a b c : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧ (unipMat a b c : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
      (unipMat a b c : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0
    simp [unipMat]

theorem flagN_unipMat (a b c : ℤ) : flagN (unipMat a b c) = ((a : ℝ), (b : ℝ), (c : ℝ)) := by
  simp [flagN, unipMat]

theorem flagN_range (hN : 3 ≤ N) {γ : SL(3, ℤ)} (hγ : γ ∈ flagGroup N) :
    ∃ i j k : ℤ, flagN γ = ((N : ℝ) * i, (N : ℝ) * j, (N : ℝ) * k) := by
  obtain ⟨-, -, -, ⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩⟩ := flag_entries hN hγ
  refine ⟨i, j, k, ?_⟩
  simp [flagN, hi, hj, hk]

/-- **The flag group `Γ_B` acting on the Heisenberg chart by left translation** (through its Malcev coordinates). -/
def flagLat (hN : 3 ≤ N) : LatticeAction (flagGroup N) where
  nOf g := flagN g.1
  nOf_mul g h := flagN_mul hN g.2 h.2

/-- The generators `(N, 0, 0)`, `(0, N, 0)`, `(0, 0, N)` of the lattice lie in `Γ_B`. -/
theorem flag_gens (hN : 3 ≤ N) :
    ∃ ga gb gc : flagGroup N, (flagLat hN).nOf ga = ((N : ℝ), 0, 0) ∧ (flagLat hN).nOf gb = (0, (N : ℝ), 0) ∧
      (flagLat hN).nOf gc = (0, 0, (N : ℝ)) := by
  refine ⟨⟨unipMat N 0 0, unipMat_mem dvd_rfl (dvd_zero _) (dvd_zero _)⟩,
    ⟨unipMat 0 N 0, unipMat_mem (dvd_zero _) dvd_rfl (dvd_zero _)⟩,
    ⟨unipMat 0 0 N, unipMat_mem (dvd_zero _) (dvd_zero _) dvd_rfl⟩, ?_, ?_, ?_⟩ <;>
  · show flagN _ = _
    simp [flagN_unipMat]

theorem flag_range (hN : 3 ≤ N) (g : flagGroup N) :
    ∃ i j k : ℤ, (flagLat hN).nOf g = ((N : ℝ) * i, (N : ℝ) * j, (N : ℝ) * k) :=
  flagN_range hN g.2

end Gens

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
