module

public import Mathlib

@[expose] public section


/-!
# One-variable contractions on the group ring of `ℤ²`

Formalized by Claude Sonnet 5.5.

`R = (Fin 2 → ℤ) →₀ ℚ` is the group ring of `ℤ²` (additive notation).  `Tm i` is multiplication by `t_i`,
`epsi i` sets the `i`-th coordinate to zero, and `sh i` is the contraction `t_i^n ↦ (t_i^n - 1)/(t_i - 1)` of the
one-variable resolution `ℚ[ℤ] →(t-1) ℚ[ℤ] → ℚ`: `(Tm i - 1) (sh i f) = f - epsi i f` (`Tm_sub_sh`) and
`sh i (Tm i f - f) = f` (`sh_Tm_sub`).  These are the ingredients of the explicit `ℚ`-linear contraction of the Koszul complex.
-/

open Finset

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomologyDescent

/-- Signed partial sums of `f` from `0` to `n`. -/
def Gsum {A : Type*} [AddCommGroup A] (f : ℤ → A) : ℤ → A
  | Int.ofNat m => ∑ k ∈ range m, f k
  | Int.negSucc m => -∑ k ∈ range (m + 1), f (-(k + 1 : ℤ))

theorem Gsum_zero {A : Type*} [AddCommGroup A] (f : ℤ → A) : Gsum f 0 = 0 := by
  simp [Gsum]

theorem Gsum_succ {A : Type*} [AddCommGroup A] (f : ℤ → A) (n : ℤ) : Gsum f (n + 1) = Gsum f n + f n := by
  rcases n with m | m
  · show ∑ k ∈ range (m + 1), f k = ∑ k ∈ range m, f k + f m
    rw [sum_range_succ]
  · rcases m with _ | m
    · have : Int.negSucc 0 + 1 = 0 := rfl
      rw [this]
      simp [Gsum]
    · have : Int.negSucc (m + 1) + 1 = Int.negSucc m := rfl
      have e : (Int.negSucc (m + 1)) = -(((m + 1 : ℕ) : ℤ) + 1) := Int.negSucc_eq _
      rw [this]
      show -∑ k ∈ range (m + 1), f (-(k + 1 : ℤ)) =
        -∑ k ∈ range (m + 1 + 1), f (-(k + 1 : ℤ)) + f (Int.negSucc (m + 1))
      rw [sum_range_succ _ (m + 1), e]
      push_cast
      abel

theorem Gsum_pred {A : Type*} [AddCommGroup A] (f : ℤ → A) (n : ℤ) : Gsum f (n - 1) = Gsum f n - f (n - 1) := by
  have := Gsum_succ f (n - 1)
  rw [sub_add_cancel] at this
  rw [this]; abel

/-- The `ℚ`-group ring of `ℤ²` (additive notation). -/
abbrev R := (Fin 2 → ℤ) →₀ ℚ

/-- Multiplication by `t_i`. -/
def Tm (i : Fin 2) : R →ₗ[ℚ] R := Finsupp.lmapDomain ℚ ℚ (fun v => v + Pi.single i 1)

/-- Setting the `i`-th coordinate to zero. -/
def epsi (i : Fin 2) : R →ₗ[ℚ] R := Finsupp.lmapDomain ℚ ℚ (fun v => Function.update v i 0)

/-- Basic family: `f_v k = [v with i-th coordinate replaced by k]`. -/
def fam (i : Fin 2) (v : Fin 2 → ℤ) (k : ℤ) : R := Finsupp.single (Function.update v i k) 1

/-- The one-variable contraction `s_i`: `s_i (t^n) = (t^n - 1)/(t - 1)`. -/
def sh (i : Fin 2) : R →ₗ[ℚ] R :=
  Finsupp.lsum ℚ fun v => LinearMap.toSpanSingleton ℚ R (Gsum (fam i v) (v i))

theorem Tm_single (i : Fin 2) (v : Fin 2 → ℤ) (r : ℚ) :
    Tm i (Finsupp.single v r) = Finsupp.single (v + Pi.single i 1) r := by
  simp [Tm]

theorem epsi_single (i : Fin 2) (v : Fin 2 → ℤ) (r : ℚ) :
    epsi i (Finsupp.single v r) = Finsupp.single (Function.update v i 0) r := by
  simp [epsi]

theorem sh_single (i : Fin 2) (v : Fin 2 → ℤ) (r : ℚ) :
    sh i (Finsupp.single v r) = r • Gsum (fam i v) (v i) := by
  simp [sh]

theorem Tm_fam (i : Fin 2) (v : Fin 2 → ℤ) (k : ℤ) : Tm i (fam i v k) = fam i v (k + 1) := by
  rw [fam, Tm_single, fam]
  congr 2
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem Tm_Gsum (i : Fin 2) (v : Fin 2 → ℤ) (n : ℤ) :
    Tm i (Gsum (fam i v) n) - Gsum (fam i v) n = fam i v n - fam i v 0 := by
  induction n using Int.induction_on with
  | zero => simp [Gsum_zero]
  | succ n ih =>
    rw [Gsum_succ, map_add, Tm_fam]
    have : Tm i (Gsum (fam i v) n) = Gsum (fam i v) n + (fam i v n - fam i v 0) := by
      rw [← ih]; abel
    rw [this]
    abel
  | pred n ih =>
    rw [Gsum_pred, map_sub]
    have e : Tm i (fam i v (-(n : ℤ) - 1)) = fam i v (-(n : ℤ)) := by
      rw [Tm_fam]; congr 1; ring
    rw [e]
    have : Tm i (Gsum (fam i v) (-(n : ℤ))) = Gsum (fam i v) (-(n : ℤ)) + (fam i v (-(n : ℤ)) - fam i v 0) := by
      rw [← ih]; abel
    rw [this]
    abel


/-- The augmentation. -/
def aug : R →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun _ : Fin 2 → ℤ => (1 : ℚ))

theorem aug_single (v : Fin 2 → ℤ) (r : ℚ) : aug (Finsupp.single v r) = r := by
  simp [aug]

theorem map_Gsum {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) (f : ℤ → A) (n : ℤ) :
    φ (Gsum f n) = Gsum (fun k => φ (f k)) n := by
  rcases n with m | m
  · simp [Gsum, map_sum]
  · simp [Gsum, map_sum]

theorem update_add_single (v : Fin 2 → ℤ) (i : Fin 2) (k : ℤ) :
    Function.update (v + Pi.single i 1) i k = Function.update v i k := by
  funext l
  by_cases hl : l = i
  · subst hl; simp
  · simp [hl]

theorem sh_Tm_sub (i : Fin 2) (f : R) : sh i (Tm i f - f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    have : Tm i (a + b) - (a + b) = (Tm i a - a) + (Tm i b - b) := by rw [map_add]; abel
    rw [this, map_add, ha, hb]
  | single v r =>
    rw [Tm_single, map_sub, sh_single, sh_single]
    have h1 : fam i (v + Pi.single i 1) = fam i v := by
      funext k; simp only [fam, update_add_single]
    have h2 : (v + Pi.single i 1 : Fin 2 → ℤ) i = v i + 1 := by simp
    rw [h1, h2, Gsum_succ, ← smul_sub, add_sub_cancel_left]
    simp [fam]

theorem Tm_sub_sh (i : Fin 2) (f : R) : Tm i (sh i f) - sh i f = f - epsi i f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    have : Tm i (sh i (a + b)) - sh i (a + b) = (Tm i (sh i a) - sh i a) + (Tm i (sh i b) - sh i b) := by
      rw [map_add, map_add]; abel
    rw [this, ha, hb, map_add]; abel
  | single v r =>
    rw [sh_single, epsi_single, map_smul, ← smul_sub, Tm_Gsum]
    have h0 : fam i v 0 = Finsupp.single (Function.update v i 0) 1 := rfl
    have h1 : fam i v (v i) = Finsupp.single v 1 := by simp [fam]
    rw [h1, h0]
    simp [smul_sub, Finsupp.smul_single]

theorem sh_Tm_comm (i j : Fin 2) (h : i ≠ j) (f : R) : sh i (Tm j f) = Tm j (sh i f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add]
  | single v r =>
    rw [Tm_single, sh_single, sh_single, map_smul]
    have h1 : fam i (v + Pi.single j 1) = fun k => Tm j (fam i v k) := by
      funext k
      simp only [fam, Tm_single]
      congr 2
      funext l
      by_cases hl : l = i
      · subst hl; simp [h]
      · by_cases hj : l = j
        · subst hj; simp [hl]
        · simp [hl, hj]
    have h2 : (v + Pi.single j 1 : Fin 2 → ℤ) i = v i := by simp [h]
    have h3 := map_Gsum (Tm j).toAddMonoidHom (fam i v) (v i)
    rw [h1, h2]
    congr 1
    exact h3.symm

theorem epsi_Tm_comm (i j : Fin 2) (h : i ≠ j) (f : R) : epsi i (Tm j f) = Tm j (epsi i f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add]
  | single v r =>
    rw [Tm_single, epsi_single, epsi_single, Tm_single]
    congr 2
    funext l
    by_cases hl : l = i
    · subst hl; simp [h]
    · by_cases hj : l = j
      · subst hj; simp [hl]
      · simp [hl, hj]

theorem epsi_Tm_sub (i : Fin 2) (f : R) : epsi i (Tm i f - f) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    have : Tm i (a + b) - (a + b) = (Tm i a - a) + (Tm i b - b) := by rw [map_add]; abel
    rw [this, map_add, ha, hb, add_zero]
  | single v r =>
    rw [Tm_single, map_sub, epsi_single, epsi_single, update_add_single, sub_self]

theorem epsi_epsi_same (i : Fin 2) (f : R) : epsi i (epsi i f) = epsi i f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single v r => rw [epsi_single, epsi_single]; simp

theorem epsi_one_epsi_zero (f : R) :
    epsi 1 (epsi 0 f) = aug f • Finsupp.single 0 1 := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, add_smul]
  | single v r =>
    rw [epsi_single, epsi_single, aug_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    funext l
    fin_cases l <;> simp



end TernaryPeriodPolynomials.Argument.GroupHomologyDescent
