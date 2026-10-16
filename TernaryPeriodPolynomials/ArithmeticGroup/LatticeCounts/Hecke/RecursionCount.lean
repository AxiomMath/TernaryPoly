module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.Operator
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.HermiteCount

@[expose] public section


/-!
# Hecke recursion: the counting identity

Formalized by Claude Sonnet 5.5.

`pair_sum`: for every function `g` of Hermite triples, `∑_{t of index p} ∑_{s of index p^{r+1}} g(red(s t)) = ∑_{T of index p^{r+2}} g T + p ∑_{T' of index p^r} g(p T')`, by the three parts `partA`, `partB1`, `innerB2` (dilation, the coset with `a = 1`, and the cosets with `p ∣ a`).
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion

open Finset Matrix TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator

/-- The Hermite triple of the product of the lattice matrices `s ∘ t`, reduced modulo the translation `z ↦ z + 1`. -/
def redP (s t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (s.1 * t.1, (s.1 * t.2.1 + s.2.1 * t.2.2) % (s.2.2 * t.2.2), s.2.2 * t.2.2)

variable {M : Type*} [AddCommMonoid M] {p : ℕ}

theorem eq_one_or_dvd {p r a : ℕ} (hp : p.Prime) (h : a ∣ p ^ r) : a = 1 ∨ p ∣ a := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 h
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · left; simp
  · right; exact dvd_pow_self p hpos.ne'

/-- Part A: the dilation `(p, 0, 1)` composed with `s`. -/
theorem partA (hp : p.Prime) {r : ℕ} (g : ℕ × ℕ × ℕ → M) :
    ∑ s ∈ hnfData (p ^ r), g (redP s (p, 0, 1)) =
      ∑ T ∈ (hnfData (p ^ (r + 1))).filter (fun T => T.1 ≠ 1), g T := by
  have hp0 : 0 < p := hp.pos
  have hr : 0 < p ^ r := pow_pos hp0 r
  have hr1 : 0 < p ^ (r + 1) := pow_pos hp0 (r + 1)
  refine Finset.sum_nbij' (fun s => (s.1 * p, s.2.1, s.2.2)) (fun T => (T.1 / p, T.2.1, T.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [mem_hnfData hr] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    rw [mem_filter, mem_hnfData hr1]
    refine ⟨⟨Nat.mul_pos h1 hp0, ?_, h3⟩, ?_⟩
    · show s.1 * p * s.2.2 = p ^ (r + 1)
      calc s.1 * p * s.2.2 = p * (s.1 * s.2.2) := by ring
        _ = p ^ (r + 1) := by rw [h2]; ring
    · show s.1 * p ≠ 1
      intro h
      have := Nat.eq_one_of_mul_eq_one_left h
      exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_left h)
  · intro T hT
    rw [mem_filter, mem_hnfData hr1] at hT
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hT
    have hdvd : T.1 ∣ p ^ (r + 1) := ⟨T.2.2, h2.symm⟩
    have hpA : p ∣ T.1 := (eq_one_or_dvd hp hdvd).resolve_left h4
    obtain ⟨A', hA'⟩ := hpA
    rw [mem_hnfData hr]
    have hA'pos : 0 < A' := by
      rcases Nat.eq_zero_or_pos A' with h | h
      · rw [h] at hA'; omega
      · exact h
    refine ⟨?_, ?_, h3⟩
    · show 0 < T.1 / p
      rw [hA', Nat.mul_div_cancel_left _ hp0]; exact hA'pos
    · show T.1 / p * T.2.2 = p ^ r
      rw [hA', Nat.mul_div_cancel_left _ hp0]
      rw [hA'] at h2
      have : p * (A' * T.2.2) = p * p ^ r := by rw [← pow_succ']; rw [← h2]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
  · intro s hs
    show (s.1 * p / p, s.2.1, s.2.2) = s
    rw [Nat.mul_div_cancel _ hp0]
  · intro T hT
    rw [mem_filter, mem_hnfData hr1] at hT
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hT
    have hdvd : T.1 ∣ p ^ (r + 1) := ⟨T.2.2, h2.symm⟩
    have hpA : p ∣ T.1 := (eq_one_or_dvd hp hdvd).resolve_left h4
    show (T.1 / p * p, T.2.1, T.2.2) = T
    rw [Nat.div_mul_cancel hpA]
  · intro s hs
    rw [mem_hnfData hr] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    congr 1
    simp only [redP, mul_zero, zero_add, mul_one]
    rw [Nat.mod_eq_of_lt h3]

theorem filter_one_mem {p r : ℕ} (hp : p.Prime) (s : ℕ × ℕ × ℕ) :
    s ∈ (hnfData (p ^ r)).filter (fun T => T.1 = 1) ↔ s.1 = 1 ∧ s.2.2 = p ^ r ∧ s.2.1 < p ^ r := by
  have hr : 0 < p ^ r := pow_pos hp.pos r
  rw [mem_filter, mem_hnfData hr]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    rw [h4, one_mul] at h2
    exact ⟨h4, h2, h2 ▸ h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by omega, by rw [h1, h2, one_mul], h2 ▸ h3⟩, h1⟩

/-- Part B1: the translates `(1, j, p)` composed with `s = (1, b, p^r)`. -/
theorem partB1 (hp : p.Prime) {r : ℕ} (g : ℕ × ℕ × ℕ → M) :
    ∑ j ∈ range p, ∑ s ∈ (hnfData (p ^ r)).filter (fun T => T.1 = 1), g (redP s (1, j, p)) =
      ∑ T ∈ (hnfData (p ^ (r + 1))).filter (fun T => T.1 = 1), g T := by
  have hp0 : 0 < p := hp.pos
  have hlt : ∀ j b : ℕ, j < p → b < p ^ r → j + b * p < p ^ (r + 1) := fun j b hj hb => by
    calc j + b * p < p + b * p := by omega
      _ = (b + 1) * p := by ring
      _ ≤ p ^ r * p := Nat.mul_le_mul_right p hb
      _ = p ^ (r + 1) := by ring
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => ((1 : ℕ), x.1 + x.2.2.1 * p, p ^ (r + 1)))
    (fun T => (T.2.1 % p, ((1 : ℕ), T.2.1 / p, p ^ r))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, s⟩ hjs
    rw [mem_product, mem_range, filter_one_mem hp] at hjs
    obtain ⟨hj, h1, h2, h3⟩ := hjs
    dsimp only at hj h1 h2 h3
    rw [filter_one_mem hp]
    exact ⟨rfl, rfl, hlt j _ hj h3⟩
  · intro T hT
    rw [filter_one_mem hp] at hT
    obtain ⟨h1, h2, h3⟩ := hT
    rw [mem_product, mem_range, filter_one_mem hp]
    refine ⟨Nat.mod_lt _ hp0, rfl, rfl, ?_⟩
    show T.2.1 / p < p ^ r
    rw [Nat.div_lt_iff_lt_mul hp0]
    calc T.2.1 < p ^ (r + 1) := h3
      _ = p ^ r * p := by ring
  · rintro ⟨j, s⟩ hjs
    rw [mem_product, mem_range, filter_one_mem hp] at hjs
    obtain ⟨hj, h1, h2, h3⟩ := hjs
    dsimp only at hj h1 h2 h3
    show (((j + s.2.1 * p) % p, ((1 : ℕ), (j + s.2.1 * p) / p, p ^ r)) : ℕ × ℕ × ℕ × ℕ) = (j, s)
    have hmod : (j + s.2.1 * p) % p = j := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have hdiv : (j + s.2.1 * p) / p = s.2.1 := by
      rw [Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hj, zero_add]
    rw [hmod, hdiv]
    obtain ⟨a, b, d⟩ := s
    simp only at h1 h2 ⊢
    rw [h1, h2]
  · intro T hT
    rw [filter_one_mem hp] at hT
    obtain ⟨h1, h2, h3⟩ := hT
    show ((1 : ℕ), T.2.1 % p + T.2.1 / p * p, p ^ (r + 1)) = T
    rw [Nat.mod_add_div' T.2.1 p]
    obtain ⟨a, b, d⟩ := T
    simp only at h1 h2 ⊢
    rw [h1, h2]
  · rintro ⟨j, s⟩ hjs
    rw [mem_product, mem_range, filter_one_mem hp] at hjs
    obtain ⟨hj, h1, h2, h3⟩ := hjs
    dsimp only at hj h1 h2 h3
    show g (redP s (1, j, p)) = g (1, j + s.2.1 * p, p ^ (r + 1))
    congr 1
    obtain ⟨a, b, d⟩ := s
    simp only at h1 h2 h3
    subst h1 h2
    simp only [redP, one_mul]
    rw [show p ^ r * p = p ^ (r + 1) by ring, Nat.mod_eq_of_lt (hlt j b hj h3)]


theorem mod_shift_left (d x b : ℕ) (hd : 0 < d) (hb : b < d) : ((x + b) % d + (d - x % d)) % d = b := by
  have hm : x % d < d := Nat.mod_lt _ hd
  have h1 : (x + b) % d = (x % d + b) % d := by rw [Nat.add_mod, Nat.mod_eq_of_lt hb]
  rw [h1]
  generalize x % d = m at hm ⊢
  by_cases h : m + b < d
  · rw [Nat.mod_eq_of_lt h]
    have : m + b + (d - m) = b + d := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  · have h' : d ≤ m + b := by omega
    have h2 : (m + b) % d = m + b - d := by
      rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    have : m + b - d + (d - m) = b := by omega
    rw [this, Nat.mod_eq_of_lt hb]

theorem mod_shift_right (d x c : ℕ) (hd : 0 < d) (hc : c < d) : (x + (c + (d - x % d)) % d) % d = c := by
  have hm : x % d < d := Nat.mod_lt _ hd
  have h1 : (x + (c + (d - x % d)) % d) % d = (x % d + (c + (d - x % d))) % d := by
    rw [Nat.add_mod_mod, Nat.mod_add_mod]
  rw [h1]
  generalize x % d = m at hm ⊢
  have : m + (c + (d - m)) = c + d := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hc]

/-- Part B2: the translates composed with `s = (a, b, d)`, `p ∣ a`, give each scaled triple once for every translate. -/
theorem innerB2 (hp : p.Prime) {r : ℕ} (g : ℕ × ℕ × ℕ → M) (j : ℕ) :
    ∑ s ∈ (hnfData (p ^ (r + 1))).filter (fun T => T.1 ≠ 1), g (redP s (1, j, p)) =
      ∑ T ∈ hnfData (p ^ r), g (p * T.1, p * T.2.1, p * T.2.2) := by
  have hp0 : 0 < p := hp.pos
  have hr : 0 < p ^ r := pow_pos hp0 r
  have hr1 : 0 < p ^ (r + 1) := pow_pos hp0 (r + 1)
  refine Finset.sum_nbij' (fun s => (s.1 / p, (s.1 / p * j + s.2.1) % s.2.2, s.2.2))
    (fun T => (p * T.1, (T.2.1 + (T.2.2 - (T.1 * j) % T.2.2)) % T.2.2, T.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [mem_filter, mem_hnfData hr1] at hs
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hs
    have hdvd : s.1 ∣ p ^ (r + 1) := ⟨s.2.2, h2.symm⟩
    obtain ⟨A', hA'⟩ := (eq_one_or_dvd hp hdvd).resolve_left h4
    have hA'pos : 0 < A' := by
      rcases Nat.eq_zero_or_pos A' with h | h
      · rw [h] at hA'; omega
      · exact h
    have hd0 : 0 < s.2.2 := by omega
    rw [mem_hnfData hr]
    refine ⟨?_, ?_, Nat.mod_lt _ hd0⟩
    · show 0 < s.1 / p
      rw [hA', Nat.mul_div_cancel_left _ hp0]; exact hA'pos
    · show s.1 / p * s.2.2 = p ^ r
      rw [hA', Nat.mul_div_cancel_left _ hp0]
      rw [hA'] at h2
      have : p * (A' * s.2.2) = p * p ^ r := by rw [← pow_succ']; rw [← h2]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
  · intro T hT
    rw [mem_hnfData hr] at hT
    obtain ⟨h1, h2, h3⟩ := hT
    rw [mem_filter, mem_hnfData hr1]
    refine ⟨⟨Nat.mul_pos hp0 h1, ?_, Nat.mod_lt _ (by omega)⟩, ?_⟩
    · show p * T.1 * T.2.2 = p ^ (r + 1)
      calc p * T.1 * T.2.2 = p * (T.1 * T.2.2) := by ring
        _ = p ^ (r + 1) := by rw [h2]; ring
    · show p * T.1 ≠ 1
      intro h
      exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h)
  · intro s hs
    rw [mem_filter, mem_hnfData hr1] at hs
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hs
    have hdvd : s.1 ∣ p ^ (r + 1) := ⟨s.2.2, h2.symm⟩
    have hpA := (eq_one_or_dvd hp hdvd).resolve_left h4
    have hd0 : 0 < s.2.2 := by omega
    obtain ⟨a, b, d⟩ := s
    simp only at h1 h2 h3 hd0 hpA ⊢
    have e1 : p * (a / p) = a := Nat.mul_div_cancel' hpA
    have e2 := mod_shift_left d (a / p * j) b hd0 h3
    rw [e1, e2]
  · intro T hT
    rw [mem_hnfData hr] at hT
    obtain ⟨h1, h2, h3⟩ := hT
    obtain ⟨a, b, d⟩ := T
    simp only at h1 h2 h3 ⊢
    have hd0 : 0 < d := by omega
    have e1 : p * a / p = a := Nat.mul_div_cancel_left _ hp0
    have e2 := mod_shift_right d (a * j) b hd0 h3
    rw [e1, e2]
  · intro s hs
    rw [mem_filter, mem_hnfData hr1] at hs
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hs
    have hdvd : s.1 ∣ p ^ (r + 1) := ⟨s.2.2, h2.symm⟩
    obtain ⟨A', hA'⟩ := (eq_one_or_dvd hp hdvd).resolve_left h4
    obtain ⟨a, b, d⟩ := s
    simp only at hA' ⊢
    subst hA'
    congr 1
    simp only [redP, mul_one]
    rw [Nat.mul_div_cancel_left _ hp0]
    have : p * A' * j + b * p = p * (A' * j + b) := by ring
    rw [this, mul_comm d p, Nat.mul_mod_mul_left]

/-- **The counting identity behind `T_p T_{p^{r+1}} = T_{p^{r+2}} + p^{k-1} T_{p^r}`**: the Hermite triples of the products of the index-`p`
triples with the index-`p^{r+1}` triples (reduced modulo translation) cover the triples of index `p^{r+2}` once and the `p`-fold scalings of
the triples of index `p^r` `p` times. -/
theorem pair_sum (hp : p.Prime) {r : ℕ} (g : ℕ × ℕ × ℕ → M) :
    ∑ t ∈ hnfData (p ^ 1), ∑ s ∈ hnfData (p ^ (r + 1)), g (redP s t) =
      ∑ T ∈ hnfData (p ^ (r + 2)), g T + p • ∑ T ∈ hnfData (p ^ r), g (p * T.1, p * T.2.1, p * T.2.2) := by
  have hp0 : 0 < p := hp.pos
  rw [hnfData_prime hp, Finset.sum_insert, Finset.sum_image]
  · rw [partA hp g]
    have hB : ∑ j : Fin p, ∑ s ∈ hnfData (p ^ (r + 1)), g (redP s (1, j.val, p)) =
        ∑ T ∈ (hnfData (p ^ (r + 2))).filter (fun T => T.1 = 1), g T +
          p • ∑ T ∈ hnfData (p ^ r), g (p * T.1, p * T.2.1, p * T.2.2) := by
      rw [← Finset.sum_range (fun j => ∑ s ∈ hnfData (p ^ (r + 1)), g (redP s (1, j, p)))]
      have hsplit : ∀ j : ℕ, ∑ s ∈ hnfData (p ^ (r + 1)), g (redP s (1, j, p)) =
          ∑ s ∈ (hnfData (p ^ (r + 1))).filter (fun T => T.1 = 1), g (redP s (1, j, p)) +
            ∑ s ∈ (hnfData (p ^ (r + 1))).filter (fun T => ¬ T.1 = 1), g (redP s (1, j, p)) := fun j =>
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      simp only [hsplit, Finset.sum_add_distrib]
      rw [partB1 hp g]
      congr 1
      have : ∀ j : ℕ, ∑ s ∈ (hnfData (p ^ (r + 1))).filter (fun T => ¬ T.1 = 1), g (redP s (1, j, p)) =
          ∑ T ∈ hnfData (p ^ r), g (p * T.1, p * T.2.1, p * T.2.2) := fun j => innerB2 hp g j
      simp only [this, Finset.sum_const, Finset.card_range]
    rw [hB, ← Finset.sum_filter_add_sum_filter_not (hnfData (p ^ (r + 2))) (fun T => T.1 = 1) g]
    abel
  · intro x _ y _ hxy
    exact Fin.ext (by simpa using congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) hxy)
  · rw [mem_image]
    rintro ⟨j, -, h⟩
    simp only [Prod.mk.injEq] at h
    exact hp.one_lt.ne h.1

end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion
