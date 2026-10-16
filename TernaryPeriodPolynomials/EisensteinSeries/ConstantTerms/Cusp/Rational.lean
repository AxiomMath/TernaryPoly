module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cusp.Instance
public import Mathlib.Algebra.GCDMonoid.Finset

@[expose] public section


/-!
# Proposition C.4 at rational plane cusps `g P g⁻¹`, `g ∈ GL₃(ℚ)`

Two ways to transport the construction to a rational plane cusp.

* `CuspData.ofRational g`: the inverse of `g`, rescaled to determinant one (a real cube root of the
  inverse determinant), with the third row cleared of denominators. The parametric series theorems
  apply to it unchanged.
* `rational_cusp_stabilizer`: every rational plane cusp is an integral one. There is an integral
  change of basis `h ∈ SL₃(ℤ)` with `h g ∈ P(ℚ)` (so `g P g⁻¹ = h⁻¹ P h`) such that an integral `p`
  lies in `g P(ℚ) g⁻¹` iff it lies in `h⁻¹ P(ℚ) h`. This uses the completion of a primitive integral
  row to a matrix of `SL₃(ℤ)` (`exists_SL3_bottom_row`) and the row `w = e₃ᵀ g⁻¹` with `w g = e₃`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped MatrixGroups
open Matrix

theorem exists_cube_root (d : ℝ) : ∃ c : ℝ, c ^ 3 = d := by
  rcases le_total 0 d with h | h
  · refine ⟨d ^ ((1 : ℝ) / 3), ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul h]
    norm_num
  · refine ⟨-((-d) ^ ((1 : ℝ) / 3)), ?_⟩
    have h' : 0 ≤ -d := by linarith
    have : ((-d) ^ ((1 : ℝ) / 3)) ^ 3 = -d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h']
      norm_num
    calc (-((-d) ^ ((1 : ℝ) / 3))) ^ 3 = -(((-d) ^ ((1 : ℝ) / 3)) ^ 3) := by ring
      _ = d := by rw [this]; ring

/-- The real matrix `g⁻¹` of a rational change of basis. -/
def ratInv (g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).map (Rat.cast : ℚ → ℝ)

theorem ratInv_det_ne_zero (g : GL (Fin 3) ℚ) : (ratInv g).det ≠ 0 := by
  have h : (ratInv g).det = (((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).det : ℚ) := by
    exact (RingHom.map_det (Rat.castHom ℝ) _).symm
  rw [h]
  have := (g⁻¹ : GL (Fin 3) ℚ).det.ne_zero
  exact_mod_cast this

/-- A real number whose cube is `det (g⁻¹)⁻¹`. -/
def ratScale (g : GL (Fin 3) ℚ) : ℝ := (exists_cube_root (ratInv g).det⁻¹).choose

theorem ratScale_cube (g : GL (Fin 3) ℚ) : ratScale g ^ 3 = (ratInv g).det⁻¹ :=
  (exists_cube_root (ratInv g).det⁻¹).choose_spec

/-- The third row of `g⁻¹`. -/
def ratRow (g : GL (Fin 3) ℚ) (j : Fin 3) : ℚ := ((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) 2 j

/-- A common denominator of the third row of `g⁻¹`. -/
def ratDen (g : GL (Fin 3) ℚ) : ℕ := ∏ l, (ratRow g l).den

/-- The plane cusp `g P g⁻¹` of a rational change of basis `g ∈ GL₃(ℚ)`: `a` is the inverse of `g`
rescaled to determinant one, and `r` clears the denominators of its third row. -/
def CuspData.ofRational (g : GL (Fin 3) ℚ) : CuspData where
  a := ratScale g • ratInv g
  det_a := by
    rw [Matrix.det_smul, Fintype.card_fin, ratScale_cube]
    exact inv_mul_cancel₀ (ratInv_det_ne_zero g)
  r := fun j => (ratRow g j).num * ((ratDen g / (ratRow g j).den : ℕ) : ℤ)
  lam := ratScale g / (ratDen g : ℝ)
  row_a j := by
    have hdvd : (ratRow g j).den ∣ ratDen g := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have hDpos : 0 < ratDen g := Finset.prod_pos fun l _ => Rat.den_pos _
    have hden : ((ratRow g j).den : ℝ) ≠ 0 := by exact_mod_cast (ratRow g j).den_nz
    have hD : (ratDen g : ℝ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have hmul : ((ratDen g / (ratRow g j).den : ℕ) : ℝ) * (ratRow g j).den = ratDen g := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hqr : ((ratRow g j : ℚ) : ℝ) = (ratRow g j).num / (ratRow g j).den := by
      exact_mod_cast (Rat.num_div_den (ratRow g j)).symm
    show (ratScale g • ratInv g) 2 j = _
    have e : ratInv g 2 j = ((ratRow g j : ℚ) : ℝ) := rfl
    rw [Matrix.smul_apply, smul_eq_mul, e, hqr]
    simp only [Int.cast_mul, Int.cast_natCast]
    field_simp
    rw [← hmul]
    ring

/-- A primitive integral row (coprime entries) is the bottom row of a matrix of `SL₃(ℤ)`. -/
theorem exists_SL3_bottom_row (a b c : ℤ) (h : Int.gcd (Int.gcd a b) c = 1) :
    ∃ H : SL(3, ℤ), (H : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = a ∧ (H : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = b ∧
      (H : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = c := by
  by_cases hd : Int.gcd a b = 0
  · -- `a = b = 0` and `c = ±1`
    obtain ⟨ha, hb⟩ := Int.gcd_eq_zero_iff.1 hd
    rw [hd] at h
    have hc : c = 1 ∨ c = -1 := by
      have : Int.natAbs c = 1 := by simpa using h
      omega
    have hdet : c * c = 1 := by rcases hc with rfl | rfl <;> norm_num
    refine ⟨⟨!![1, 0, 0; 0, c, 0; 0, 0, c], ?_⟩, ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_three]; simp; linear_combination hdet
    · simp [ha]
    · simp [hb]
    · simp
  · have hdpos : 0 < Int.gcd a b := Nat.pos_of_ne_zero hd
    have hab := Int.isCoprime_iff_gcd_eq_one.2 (Int.gcd_div_gcd_div_gcd hdpos)
    have hdc : IsCoprime ((Int.gcd a b : ℕ) : ℤ) c := Int.isCoprime_iff_gcd_eq_one.2 h
    obtain ⟨g, hg⟩ := hab.exists_SL2_row 1
    obtain ⟨W, hW⟩ := hdc.exists_SL2_row 1
    have hg10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = a / Int.gcd a b := by
      exact hg.1
    have hg11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = b / Int.gcd a b := by
      exact hg.2
    have hW10 : (W : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = Int.gcd a b := by
      exact hW.1
    have hW11 : (W : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = c := by
      exact hW.2
    have hga : (Int.gcd a b : ℤ) * (a / Int.gcd a b) = a := Int.mul_ediv_cancel' (Int.gcd_dvd_left a b)
    have hgb : (Int.gcd a b : ℤ) * (b / Int.gcd a b) = b := Int.mul_ediv_cancel' (Int.gcd_dvd_right a b)
    have hgd : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
      have := g.2; rwa [Matrix.det_fin_two] at this
    have hWd : (W : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (W : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (W : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (W : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
      have := W.2; rwa [Matrix.det_fin_two] at this
    refine ⟨⟨!![(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, 0;
      (W : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
      (W : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1,
      (W : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      (W : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
      (W : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1,
      (W : Matrix (Fin 2) (Fin 2) ℤ) 1 1], ?_⟩, ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp
      linear_combination ((W : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (W : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (W : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (W : Matrix (Fin 2) (Fin 2) ℤ) 1 0) * hgd + hWd
    · simp [hW10, hg10, hga]
    · simp [hW10, hg11, hgb]
    · simp [hW11]

theorem ratR_eq (g : GL (Fin 3) ℚ) (j : Fin 3) :
    (((CuspData.ofRational g).r j : ℤ) : ℚ) = (ratDen g : ℚ) * ratRow g j := by
  have hdvd : (ratRow g j).den ∣ ratDen g := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hden : ((ratRow g j).den : ℚ) ≠ 0 := by exact_mod_cast (ratRow g j).den_nz
  have hmul : ((ratDen g / (ratRow g j).den : ℕ) : ℚ) * (ratRow g j).den = ratDen g := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  have hqr : (ratRow g j : ℚ) = (ratRow g j).num / (ratRow g j).den :=
    (Rat.num_div_den (ratRow g j)).symm
  show (((ratRow g j).num * ((ratDen g / (ratRow g j).den : ℕ) : ℤ) : ℤ) : ℚ) = _
  simp only [Int.cast_mul, Int.cast_natCast]
  conv_rhs => rw [hqr]
  field_simp
  rw [← hmul]
  ring

theorem ratRow_ne_zero (g : GL (Fin 3) ℚ) : ∃ j, ratRow g j ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h0 := Matrix.det_eq_zero_of_row_eq_zero (A := ((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) 2
    hcon
  exact (g⁻¹ : GL (Fin 3) ℚ).det.ne_zero (by simpa using h0)

/-- **Every rational plane cusp is an integral one.** For `g ∈ GL₃(ℚ)` there is an integral change of
basis `h ∈ SL₃(ℤ)` with `h g` in the rational plane parabolic `P(ℚ)` (bottom row `(0, 0, t)`),
so that `g P g⁻¹ = h⁻¹ P h`. -/
theorem exists_integral_cusp (g : GL (Fin 3) ℚ) :
    ∃ (h : SL(3, ℤ)) (t : ℚ), t ≠ 0 ∧ ∀ j : Fin 3,
      (((h : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
        ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) 2 j = if j = 2 then t else 0 := by
  set r' : Fin 3 → ℤ := (CuspData.ofRational g).r with hr'
  have hDpos : 0 < ratDen g := Finset.prod_pos fun l _ => Rat.den_pos _
  obtain ⟨j0, hj0⟩ := ratRow_ne_zero g
  have hne : (Finset.univ : Finset (Fin 3)).Nonempty := Finset.univ_nonempty
  obtain ⟨r, hr, hgcd⟩ := Finset.extract_gcd r' hne
  set G : ℤ := Finset.univ.gcd r' with hG
  have hr'0 : r' j0 ≠ 0 := by
    intro h0
    have := ratR_eq g j0
    rw [← hr', h0] at this
    simp only [Int.cast_zero] at this
    have hD : (ratDen g : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    exact hj0 ((mul_eq_zero.1 this.symm).resolve_left hD)
  have hG0 : G ≠ 0 := by
    intro h0
    have := hr j0 (Finset.mem_univ _)
    rw [h0, zero_mul] at this
    exact hr'0 this
  -- the row `r` is primitive
  have hprim : Int.gcd (Int.gcd (r 0) (r 1)) (r 2) = 1 := by
    set k : ℕ := Int.gcd (Int.gcd (r 0) (r 1)) (r 2) with hk
    have hk0 : (k : ℤ) ∣ r 0 :=
      (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
    have hk1 : (k : ℤ) ∣ r 1 :=
      (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
    have hk2 : (k : ℤ) ∣ r 2 := Int.gcd_dvd_right _ _
    have hdvd : (k : ℤ) ∣ Finset.univ.gcd r := by
      refine Finset.dvd_gcd fun b _ => ?_
      fin_cases b <;> assumption
    rw [hgcd] at hdvd
    have : k = 1 := by
      have h1 : (k : ℤ) ∣ 1 := by simpa using hdvd
      exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1
    exact this
  obtain ⟨H, h0, h1, h2⟩ := exists_SL3_bottom_row (r 0) (r 1) (r 2) hprim
  refine ⟨H, (ratDen g : ℚ) / G, ?_, ?_⟩
  · have hD : (ratDen g : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have hG' : (G : ℚ) ≠ 0 := by exact_mod_cast hG0
    exact div_ne_zero hD hG'
  · intro j
    have hrow : ∀ l, (H : Matrix (Fin 3) (Fin 3) ℤ) 2 l = r l := by
      intro l; fin_cases l
      · exact h0
      · exact h1
      · exact h2
    have hrG : ∀ l, (G : ℚ) * (r l : ℚ) = (ratDen g : ℚ) * ratRow g l := by
      intro l
      have := hr l (Finset.mem_univ _)
      have h' : ((r' l : ℤ) : ℚ) = (G : ℚ) * (r l : ℚ) := by
        have := congrArg (Int.cast : ℤ → ℚ) this
        simpa using this
      rw [← h', hr']
      exact ratR_eq g l
    -- `w g = e₃`
    have hinv : ((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
        ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel]; rfl
    have hwg : ∑ l, ratRow g l * ((g : Matrix (Fin 3) (Fin 3) ℚ) l j) =
        (1 : Matrix (Fin 3) (Fin 3) ℚ) 2 j := by
      have := congrFun (congrFun hinv 2) j
      rw [Matrix.mul_apply] at this
      exact this
    have hG' : (G : ℚ) ≠ 0 := by exact_mod_cast hG0
    have hD : (ratDen g : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    rw [Matrix.mul_apply]
    have e1 : ∑ l, ((H : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) 2 l *
        ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) l j =
        ∑ l, (r l : ℚ) * ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) l j := by
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [Matrix.map_apply, hrow l]
    rw [e1]
    have e2 : (G : ℚ) * ∑ l, (r l : ℚ) * ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) l j =
        (ratDen g : ℚ) * (1 : Matrix (Fin 3) (Fin 3) ℚ) 2 j := by
      rw [Finset.mul_sum, ← hwg, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, hrG l]; ring
    have e3 : ∑ l, (r l : ℚ) * ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) l j =
        (ratDen g : ℚ) / G * (1 : Matrix (Fin 3) (Fin 3) ℚ) 2 j := by
      field_simp
      linear_combination e2
    rw [e3]
    by_cases hj : j = 2
    · subst hj; simp
    · have hj' : ¬ (2 = j) := fun h => hj h.symm
      simp [hj, hj']

/-! ### The rational plane parabolic `P(ℚ)` -/

/-- Membership in the rational plane parabolic `P(ℚ)`: bottom row `(0, 0, *)`. -/
def InPQ (M : Matrix (Fin 3) (Fin 3) ℚ) : Prop := M 2 0 = 0 ∧ M 2 1 = 0

theorem InPQ.mul {M N : Matrix (Fin 3) (Fin 3) ℚ} (hM : InPQ M) (hN : InPQ N) : InPQ (M * N) := by
  obtain ⟨hM0, hM1⟩ := hM
  obtain ⟨hN0, hN1⟩ := hN
  constructor
  · simp [Matrix.mul_apply, Fin.sum_univ_three, hM0, hM1, hN0]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, hM0, hM1, hN1]

theorem InPQ.inv {M : Matrix (Fin 3) (Fin 3) ℚ} (hM : InPQ M) : InPQ M⁻¹ := by
  obtain ⟨hM0, hM1⟩ := hM
  constructor
  · simp [Matrix.inv_def, Matrix.adjugate_fin_three, hM0, hM1]
  · simp [Matrix.inv_def, Matrix.adjugate_fin_three, hM0, hM1]

/-- **The stabilizer of a rational plane cusp is that of an integral one.** For `g ∈ GL₃(ℚ)` there
is an integral change of basis `h ∈ SL₃(ℤ)` with `h g ∈ P(ℚ)` (so `g P g⁻¹ = h⁻¹ P h`), and an
integral matrix `p` lies in `g P(ℚ) g⁻¹` (`g⁻¹ p g ∈ P(ℚ)`) iff it lies in `h⁻¹ P(ℚ) h`
(`h p h⁻¹ ∈ P(ℚ)`). -/
theorem rational_cusp_stabilizer (g : GL (Fin 3) ℚ) :
    ∃ h : SL(3, ℤ), InPQ (((h : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
        ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) ∧
      ∀ p : SL(3, ℤ),
        InPQ (((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
          ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
          ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) ↔
        InPQ (((h : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
          ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
          (((h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ))) := by
  obtain ⟨h, t, ht, hrow⟩ := exists_integral_cusp g
  set hQ : Matrix (Fin 3) (Fin 3) ℚ := (h : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ) with hhQ
  set hiQ : Matrix (Fin 3) (Fin 3) ℚ :=
    ((h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ) with hhiQ
  set gM : Matrix (Fin 3) (Fin 3) ℚ := ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) with hgM
  set gi : Matrix (Fin 3) (Fin 3) ℚ := ((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) with hgi
  have hq : InPQ (hQ * gM) := ⟨by simpa using hrow 0, by simpa using hrow 1⟩
  have hhh : hiQ * hQ = 1 := by
    have h1 : (((h⁻¹ * h : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ)) = 1 := by simp
    rw [Matrix.SpecialLinearGroup.coe_mul] at h1
    have h2 := congrArg (Int.castRingHom ℚ).mapMatrix h1
    rw [map_mul, map_one] at h2
    exact h2
  have hhh' : hQ * hiQ = 1 := by
    have h1 : (((h * h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ)) = 1 := by simp
    rw [Matrix.SpecialLinearGroup.coe_mul] at h1
    have h2 := congrArg (Int.castRingHom ℚ).mapMatrix h1
    rw [map_mul, map_one] at h2
    exact h2
  have hgg : gi * gM = 1 := by rw [hgi, hgM, ← Units.val_mul, inv_mul_cancel]; rfl
  have hgg' : gM * gi = 1 := by rw [hgi, hgM, ← Units.val_mul, mul_inv_cancel]; rfl
  refine ⟨h, hq, fun p => ?_⟩
  set pQ : Matrix (Fin 3) (Fin 3) ℚ := (p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)
  set q : Matrix (Fin 3) (Fin 3) ℚ := hQ * gM with hqdef
  have hqinv : IsUnit q.det := by
    have : q * (gi * hiQ) = 1 := by
      rw [hqdef, Matrix.mul_assoc, ← Matrix.mul_assoc gM, hgg', Matrix.one_mul, hhh']
    exact (Matrix.isUnit_det_of_right_inverse this)
  have hq' : InPQ q⁻¹ := hq.inv
  have hX1 : q⁻¹ * hQ * gM = 1 := by
    rw [Matrix.mul_assoc, ← hqdef]; exact Matrix.nonsing_inv_mul q hqinv
  have e1 : gi = q⁻¹ * hQ := by
    calc gi = 1 * gi := (Matrix.one_mul _).symm
      _ = (q⁻¹ * hQ * gM) * gi := by rw [hX1]
      _ = q⁻¹ * hQ * (gM * gi) := Matrix.mul_assoc _ _ _
      _ = q⁻¹ * hQ := by rw [hgg', Matrix.mul_one]
  have e2 : gM = hiQ * q := by
    rw [hqdef, ← Matrix.mul_assoc, hhh, Matrix.one_mul]
  have hX : gi * pQ * gM = q⁻¹ * (hQ * pQ * hiQ) * q := by
    rw [e1]
    conv_lhs => rw [e2]
    simp only [Matrix.mul_assoc]
  rw [hX]
  have hqq : q * q⁻¹ = 1 := Matrix.mul_nonsing_inv q hqinv
  constructor
  · intro hY
    have := (hq.mul hY).mul hq'
    have e : q * (q⁻¹ * (hQ * pQ * hiQ) * q) * q⁻¹ = hQ * pQ * hiQ := by
      calc q * (q⁻¹ * (hQ * pQ * hiQ) * q) * q⁻¹
          = (q * q⁻¹) * (hQ * pQ * hiQ) * (q * q⁻¹) := by simp only [Matrix.mul_assoc]
        _ = hQ * pQ * hiQ := by rw [hqq, Matrix.one_mul, Matrix.mul_one]
    rwa [e] at this
  · intro hY
    exact (hq'.mul hY).mul hq

theorem inPQ_cast_iff (X : SL(3, ℤ)) :
    InPQ ((X : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) ↔
      (X : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧ (X : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := by
  unfold InPQ
  simp only [Matrix.map_apply, eq_intCast, Int.cast_eq_zero]

theorem cast_conj (h p : SL(3, ℤ)) :
    ((h : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
      ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
      (((h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) =
      (((h * p * h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

end TernaryPeriodPolynomials.Argument.ConvergenceC4
