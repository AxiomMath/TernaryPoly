module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreStab

@[expose] public section


/-!
# Sums over a permutation of `p + 1` points with a unique fixed point and `σ ^ p = 1`

Let `σ` be a permutation of a finite type `ι` with `p + 1` points, `p` prime, such that `σ ^ p = 1`
and `σ` has exactly one fixed point `f`.  Then the remaining `p` points form a single cycle: for
every `j₁ ≠ f` the map `i ↦ (σ ^ i) j₁` is a bijection of `Fin p` onto `ι ∖ {f}`.  Consequently, for
every function `F : ι → M` to an additive commutative monoid,

  `∑ j, F j = F f + ∑ i : Fin p, F ((σ ^ i) j₁)`.

This is applied to the action `S.nextEquiv g` of a cusp element `g` on the Hecke cosets: `g ^ p`
acts trivially and `g` has a unique fixed coset.  The iterates of the coset action are
`S.next (g ^ i) j = (S.nextEquiv g ^ i) j` (`next_pow_eq`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open TernaryPeriodPolynomials.Spectral.HeckeH1

section Perm

variable {ι : Type} [Fintype ι] (σ : Equiv.Perm ι) {p : ℕ}

omit [Fintype ι] in
/-- If `σ ^ p = 1` with `p` prime and `σ ^ k` fixes `j` for some `0 < k < p`, then `σ` fixes `j`. -/
theorem fixed_of_pow_fixed (hp : p.Prime) (hpow : σ ^ p = 1) {k : ℕ} (hk0 : 0 < k) (hkp : k < p)
    {j : ι} (hj : (σ ^ k) j = j) : σ j = j := by
  have hcop : Nat.Coprime k p := by
    have : Nat.Coprime p k :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hk0 hkp)
    exact this.symm
  obtain ⟨m, _, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have h1 : ∀ n : ℕ, ((σ ^ k) ^ n) j = j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hj]
  have h2 : σ ^ (k * m) = σ := by
    have e : k * m = p * (k * m / p) + 1 := by
      have := Nat.div_add_mod (k * m) p
      rw [hm] at this
      omega
    rw [e, pow_add, pow_mul, hpow, one_pow, one_mul, pow_one]
  have := h1 m
  rw [← pow_mul, h2] at this
  exact this

omit [Fintype ι] in
/-- The points of the cycle are not fixed. -/
theorem pow_apply_ne {f : ι} (hf : σ f = f) {j₁ : ι} (hj₁ : j₁ ≠ f) (i : ℕ) :
    (σ ^ i) j₁ ≠ f := by
  have hfi : ∀ i : ℕ, (σ ^ i) f = f := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hf]
  intro h
  exact hj₁ ((σ ^ i).injective (h.trans (hfi i).symm))

omit [Fintype ι] in
/-- The map `i ↦ (σ ^ i) j₁` is injective on `Fin p`. -/
theorem pow_apply_injective (hp : p.Prime) (hpow : σ ^ p = 1) {f : ι}
    (hfix : ∀ j, σ j = j → j = f) {j₁ : ι} (hj₁ : j₁ ≠ f) :
    Function.Injective (fun i : Fin p => (σ ^ (i : ℕ)) j₁) := by
  have key : ∀ a b : ℕ, a < b → b < p → (σ ^ a) j₁ = (σ ^ b) j₁ → False := by
    intro a b hab hbp h
    have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hb, Equiv.Perm.mul_apply] at h
    have h' : (σ ^ (b - a)) j₁ = j₁ := ((σ ^ a).injective h).symm
    have := fixed_of_pow_fixed σ hp hpow (by omega) (by omega) h'
    exact hj₁ (hfix _ this)
  intro i i' h
  by_contra hne
  have hne' : (i : ℕ) ≠ i' := fun e => hne (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact key i i' hlt i'.isLt h
  · exact key i' i hlt i.isLt h.symm

/-- **Sum over a cycle plus a fixed point.** -/
theorem sum_eq_fixed_add_cycle {M : Type} [AddCommMonoid M] (hp : p.Prime) (hpow : σ ^ p = 1)
    (hcard : Fintype.card ι = p + 1) {f : ι} (hfix : ∀ j, σ j = j ↔ j = f) (F : ι → M) {j₁ : ι}
    (hj₁ : j₁ ≠ f) :
    ∑ j, F j = F f + ∑ i : Fin p, F ((σ ^ (i : ℕ)) j₁) := by
  classical
  have hfixf : σ f = f := (hfix f).mpr rfl
  have hinj := pow_apply_injective σ hp hpow (fun j hj => (hfix j).mp hj) hj₁
  have hsub : (Finset.univ.image (fun i : Fin p => (σ ^ (i : ℕ)) j₁)) ⊆ Finset.univ.erase f := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_erase.mpr ⟨pow_apply_ne σ hfixf hj₁ i, Finset.mem_univ _⟩
  have hcard1 : (Finset.univ.image (fun i : Fin p => (σ ^ (i : ℕ)) j₁)).card = p := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hcard2 : (Finset.univ.erase f).card = p := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard1, hcard2])
  rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ f), ← heq,
    Finset.sum_image (fun a _ b _ h => hinj h)]

end Perm

section Cosets

variable {G 𝔾 : Type} [Group G] [Group 𝔾] {embed : G →* 𝔾} (S : RightCosets embed)

/-- The iterates of the coset action: `S.next (g ^ i) j = (S.nextEquiv g ^ i) j`. -/
theorem next_pow_eq (g : G) (i : ℕ) (j : S.index) :
    S.next (g ^ i) j = ((S.nextEquiv g) ^ i) j := by
  induction i generalizing j with
  | zero => rw [pow_zero, pow_zero]; exact AdjCore.next_one S j
  | succ i ih =>
    rw [pow_succ, S.next_mul, pow_succ', Equiv.Perm.mul_apply, ih]
    rfl

end Cosets

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
