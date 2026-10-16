module

public import Mathlib

@[expose] public section



/-!
# A weight filtration for unipotent substitutions

Formalized by Claude Sonnet 5.5.

Give `X₀, X₁, X₂` the weights `0, 1, 2` (`wt`) and let `WJ j` be the polynomials all of whose monomials have weight `≥ j`.  The upper triangular unipotent substitution
`shearAlg α β γ : X₀ ↦ X₀ + α X₁ + β X₂, X₁ ↦ X₁ + γ X₂, X₂ ↦ X₂` maps `WJ j` into `WJ j` and raises weights: `S q - q ∈ WJ (j + 1)` for `q ∈ WJ j` (`Tp.of_mem`).
Hence `(S - 1)^k` maps everything into `WJ k`, which meets the homogeneous polynomials of degree `n` in `0` for `k > 2n`.
-/

open MvPolynomial
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

/-- The weight `w(X₀) = 0`, `w(X₁) = 1`, `w(X₂) = 2` of a monomial. -/
def wt (m : Fin 3 →₀ ℕ) : ℕ := m 1 + 2 * m 2

theorem wt_add (m₁ m₂ : Fin 3 →₀ ℕ) : wt (m₁ + m₂) = wt m₁ + wt m₂ := by
  simp only [wt, Finsupp.add_apply]; ring

/-- Polynomials all of whose monomials have weight at least `j`. -/
def WJ (j : ℕ) : Submodule ℂ (MvPolynomial (Fin 3) ℂ) where
  carrier := {q | ∀ m ∈ q.support, j ≤ wt m}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq m hm
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hp m h
    · exact hq m h
  smul_mem' := by
    intro c p hp m hm
    exact hp m (MvPolynomial.support_smul hm)

theorem mem_WJ {j : ℕ} {q : MvPolynomial (Fin 3) ℂ} : q ∈ WJ j ↔ ∀ m ∈ q.support, j ≤ wt m := Iff.rfl

theorem WJ_mono {i j : ℕ} (h : i ≤ j) : WJ j ≤ WJ i := fun _ hq m hm => h.trans (hq m hm)

theorem WJ_mul {a b : ℕ} {p q : MvPolynomial (Fin 3) ℂ} (hp : p ∈ WJ a) (hq : q ∈ WJ b) :
    p * q ∈ WJ (a + b) := by
  intro m hm
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  rw [wt_add]
  exact Nat.add_le_add (hp m₁ h₁) (hq m₂ h₂)

theorem C_mem_WJ (c : ℂ) : (C c : MvPolynomial (Fin 3) ℂ) ∈ WJ 0 := fun _ _ => Nat.zero_le _

theorem X_mem_WJ (i : Fin 3) : (X i : MvPolynomial (Fin 3) ℂ) ∈ WJ (wt (Finsupp.single i 1)) := by
  intro m hm
  rw [MvPolynomial.support_X] at hm
  simp at hm
  rw [hm]

section Shear

variable (α β γ : ℂ)

/-- **The unipotent substitution** `X₀ ↦ X₀ + α X₁ + β X₂`, `X₁ ↦ X₁ + γ X₂`, `X₂ ↦ X₂`. -/
abbrev shearAlg : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  bind₁ (![X 0 + C α * X 1 + C β * X 2, X 1 + C γ * X 2, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)

/-- `q` has weight `≥ a` and the substitution raises its weight: `S q - q` has weight `≥ a + 1`. -/
def Tp (a : ℕ) (q : MvPolynomial (Fin 3) ℂ) : Prop :=
  q ∈ WJ a ∧ shearAlg α β γ q - q ∈ WJ (a + 1)

variable {α β γ}

theorem Tp.mul {a b : ℕ} {p q : MvPolynomial (Fin 3) ℂ} (hp : Tp α β γ a p) (hq : Tp α β γ b q) :
    Tp α β γ (a + b) (p * q) := by
  refine ⟨WJ_mul hp.1 hq.1, ?_⟩
  have e : shearAlg α β γ (p * q) - p * q =
      (shearAlg α β γ p - p) * shearAlg α β γ q + p * (shearAlg α β γ q - q) := by
    rw [map_mul]; ring
  rw [e]
  have hSq : shearAlg α β γ q ∈ WJ b := by
    have : shearAlg α β γ q = q + (shearAlg α β γ q - q) := by ring
    rw [this]
    exact (WJ b).add_mem hq.1 (WJ_mono (Nat.le_succ b) hq.2)
  refine (WJ _).add_mem ?_ ?_
  · have h := WJ_mul hp.2 hSq
    rwa [show a + 1 + b = a + b + 1 by ring] at h
  · have h := WJ_mul hp.1 hq.2
    rwa [show a + (b + 1) = a + b + 1 by ring] at h

theorem Tp.const (c : ℂ) : Tp α β γ 0 (C c) := by
  refine ⟨C_mem_WJ c, ?_⟩
  simp

theorem Tp.one : Tp α β γ 0 1 := by
  simpa using Tp.const (α := α) (β := β) (γ := γ) 1

theorem Tp.pow {a : ℕ} {p : MvPolynomial (Fin 3) ℂ} (hp : Tp α β γ a p) (k : ℕ) :
    Tp α β γ (k * a) (p ^ k) := by
  induction k with
  | zero => simpa using Tp.one
  | succ k ih =>
    rw [pow_succ, show (k + 1) * a = k * a + a by ring]
    exact ih.mul hp

theorem Tp.X0 : Tp α β γ 0 (X 0) := by
  refine ⟨by simpa [wt] using X_mem_WJ (0 : Fin 3), ?_⟩
  have h1 : (C α * X 1 : MvPolynomial (Fin 3) ℂ) ∈ WJ (0 + 1) :=
    WJ_mul (a := 0) (b := 1) (C_mem_WJ α) (by simpa [wt] using X_mem_WJ (1 : Fin 3))
  have h2 : (C β * X 2 : MvPolynomial (Fin 3) ℂ) ∈ WJ (0 + 2) :=
    WJ_mul (a := 0) (b := 2) (C_mem_WJ β) (by simpa [wt] using X_mem_WJ (2 : Fin 3))
  have : shearAlg α β γ (X 0) - X 0 = C α * X 1 + C β * X 2 := by
    simp [shearAlg]
    ring
  rw [this]
  exact (WJ (0 + 1)).add_mem h1 (WJ_mono (show 0 + 1 ≤ 0 + 2 by norm_num) h2)

theorem Tp.X1 : Tp α β γ 1 (X 1) := by
  refine ⟨by simpa [wt] using X_mem_WJ (1 : Fin 3), ?_⟩
  have h2 : (C γ * X 2 : MvPolynomial (Fin 3) ℂ) ∈ WJ (0 + 2) :=
    WJ_mul (a := 0) (b := 2) (C_mem_WJ γ) (by simpa [wt] using X_mem_WJ (2 : Fin 3))
  have : shearAlg α β γ (X 1) - X 1 = C γ * X 2 := by
    simp [shearAlg]
  rw [this]
  simpa using h2

theorem Tp.X2 : Tp α β γ 2 (X 2) := by
  refine ⟨by simpa [wt] using X_mem_WJ (2 : Fin 3), ?_⟩
  have : shearAlg α β γ (X 2) - X 2 = 0 := by
    simp [shearAlg]
  rw [this]
  exact (WJ _).zero_mem

theorem Tp.monomial (m : Fin 3 →₀ ℕ) (c : ℂ) : Tp α β γ (wt m) (MvPolynomial.monomial m c) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_three]
  have h := ((Tp.const (α := α) (β := β) (γ := γ) c).mul ((Tp.X0.pow (m 0)).mul ((Tp.X1.pow (m 1)).mul
    (Tp.X2.pow (m 2)))))
  have e : 0 + (m 0 * 0 + (m 1 * 1 + m 2 * 2)) = wt m := by simp [wt]; ring
  rw [e] at h
  simpa [mul_assoc] using h

/-- **The substitution raises weights.** -/
theorem Tp.of_mem {j : ℕ} {q : MvPolynomial (Fin 3) ℂ} (hq : q ∈ WJ j) : Tp α β γ j q := by
  refine ⟨hq, ?_⟩
  have e : shearAlg α β γ q - q = ∑ m ∈ q.support, (shearAlg α β γ (MvPolynomial.monomial m (q.coeff m)) -
      MvPolynomial.monomial m (q.coeff m)) := by
    rw [Finset.sum_sub_distrib, ← map_sum, ← q.as_sum]
  rw [e]
  refine (WJ (j + 1)).sum_mem fun m hm => ?_
  have h := (Tp.monomial (α := α) (β := β) (γ := γ) m (q.coeff m)).2
  exact WJ_mono (Nat.succ_le_succ (hq m hm)) h

end Shear

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
