module

public import TernaryPeriodPolynomials.ModularForm.HeckeComposite.Series

@[expose] public section



noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open scoped BigOperators


/-- One divisor term of the composite coefficient formula. -/
def hkTerm (k : ℤ) (c : ℕ → ℂ) (x : ℕ × ℕ) (N : ℕ) : ℂ :=
  if x.1 ∣ N then (x.1 : ℂ) ^ (k - 1) * c (x.2 * (N / x.1)) else 0

theorem compositeCoeff_eq_sum (k : ℤ) (m : ℕ) (c : ℕ → ℂ) (N : ℕ) :
    compositeCoeff k m c N = ∑ x ∈ Nat.divisorsAntidiagonal m, hkTerm k c x N := rfl

theorem hkTerm_mul_left (k : ℤ) (c : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (y : ℕ × ℕ) (N : ℕ) :
    hkTerm k c (p * y.1, y.2) N =
      if p ∣ N then (p : ℂ) ^ (k - 1) * hkTerm k c y (N / p) else 0 := by
  by_cases hpN : p ∣ N
  · obtain ⟨q, rfl⟩ := hpN
    rw [ite_eq_left (dvd_mul_right p q), Nat.mul_div_cancel_left q hp.pos]
    unfold hkTerm
    dsimp only
    by_cases hy : y.1 ∣ q
    · have hdiv : p * y.1 ∣ p * q := mul_dvd_mul_left p hy
      rw [ite_eq_left hdiv, ite_eq_left hy, Nat.mul_div_mul_left q y.1 hp.pos]
      push_cast
      rw [mul_zpow]
      ring
    · have hdiv : ¬ p * y.1 ∣ p * q := fun h => hy ((Nat.mul_dvd_mul_iff_left hp.pos).mp h)
      rw [ite_eq_right hdiv, ite_eq_right hy, mul_zero]
  · rw [ite_eq_right hpN]
    unfold hkTerm
    dsimp only
    rw [ite_eq_right (fun h => hpN (dvd_trans (dvd_mul_right p y.1) h))]

theorem hkTerm_mul_mul (k : ℤ) (c : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (z : ℕ × ℕ) (N : ℕ) :
    hkTerm k c (p * z.1, z.2) (p * N) = (p : ℂ) ^ (k - 1) * hkTerm k c z N := by
  unfold hkTerm
  dsimp only
  by_cases hz : z.1 ∣ N
  · rw [ite_eq_left (mul_dvd_mul_left p hz), ite_eq_left hz, Nat.mul_div_mul_left N z.1 hp.pos]
    push_cast
    rw [mul_zpow]
    ring
  · rw [ite_eq_right (fun h => hz ((Nat.mul_dvd_mul_iff_left hp.pos).mp h)), ite_eq_right hz, mul_zero]

theorem hkTerm_mul_right_of_not_dvd (k : ℤ) (c : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (y : ℕ × ℕ)
    (hy : ¬ p ∣ y.1) (N : ℕ) :
    hkTerm k c y (p * N) = hkTerm k c (y.1, p * y.2) N := by
  have hcop : Nat.Coprime y.1 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hy).symm
  have hiff : y.1 ∣ p * N ↔ y.1 ∣ N := hcop.dvd_mul_left
  unfold hkTerm
  dsimp only
  by_cases hN : y.1 ∣ N
  · rw [ite_eq_left (hiff.mpr hN), ite_eq_left hN, Nat.mul_div_assoc p hN]
    rw [show y.2 * (p * (N / y.1)) = p * y.2 * (N / y.1) by ring]
  · rw [ite_eq_right (fun h => hN (hiff.mp h)), ite_eq_right hN]

theorem sum_hkTerm_mul_left (k : ℤ) (c : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (m N : ℕ) :
    ∑ y ∈ Nat.divisorsAntidiagonal m, hkTerm k c (p * y.1, y.2) N =
      if p ∣ N then (p : ℂ) ^ (k - 1) * compositeCoeff k m c (N / p) else 0 := by
  by_cases h : p ∣ N
  · simp only [hkTerm_mul_left k c hp, h, ite_true, compositeCoeff_eq_sum, Finset.mul_sum]
  · simp only [hkTerm_mul_left k c hp, h, ite_false, Finset.sum_const_zero]

/-- Divisor pairs of `p * m` whose first entry is divisible by `p`. -/
theorem sum_filter_dvd_mul (k : ℤ) (c : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (m N : ℕ) :
    ∑ x ∈ (Nat.divisorsAntidiagonal (p * m)).filter (fun x : ℕ × ℕ => p ∣ x.1), hkTerm k c x N =
      ∑ y ∈ Nat.divisorsAntidiagonal m, hkTerm k c (p * y.1, y.2) N := by
  refine Finset.sum_nbij' (fun x : ℕ × ℕ => (x.1 / p, x.2)) (fun y : ℕ × ℕ => (p * y.1, y.2))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨⟨hmul, hne⟩, hdvd⟩ := hx
    have key : p * (x.1 / p) = x.1 := Nat.mul_div_cancel' hdvd
    simp only [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, fun h0 => hne (by rw [h0, mul_zero])⟩
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [← mul_assoc, key, hmul]
  · intro y hy
    simp only [Nat.mem_divisorsAntidiagonal] at hy
    obtain ⟨hmul, hne⟩ := hy
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, mul_ne_zero hp.ne_zero hne⟩, dvd_mul_right p y.1⟩
    rw [mul_assoc, hmul]
  · intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨_, hdvd⟩ := hx
    show (p * (x.1 / p), x.2) = x
    exact Prod.ext (Nat.mul_div_cancel' hdvd) rfl
  · intro y _
    show (p * y.1 / p, y.2) = y
    exact Prod.ext (Nat.mul_div_cancel_left y.1 hp.pos) rfl
  · intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨_, hdvd⟩ := hx
    show hkTerm k c x N = hkTerm k c (p * (x.1 / p), x.2) N
    rw [Nat.mul_div_cancel' hdvd]

/-- Divisor pairs of `p * m` whose first entry is not divisible by `p`. -/
theorem sum_filter_not_dvd_mul (k : ℤ) (c : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (m N : ℕ) :
    ∑ x ∈ (Nat.divisorsAntidiagonal (p * m)).filter (fun x : ℕ × ℕ => ¬ p ∣ x.1),
        hkTerm k c x N =
      ∑ y ∈ (Nat.divisorsAntidiagonal m).filter (fun y : ℕ × ℕ => ¬ p ∣ y.1),
        hkTerm k c (y.1, p * y.2) N := by
  have hx2 : ∀ x : ℕ × ℕ, x ∈ Nat.divisorsAntidiagonal (p * m) → ¬ p ∣ x.1 → p ∣ x.2 := by
    intro x hx hnd
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hdiv : p ∣ x.1 * x.2 := by rw [hx.1]; exact dvd_mul_right p m
    rcases (Nat.Prime.dvd_mul hp).mp hdiv with h1 | h1
    · exact absurd h1 hnd
    · exact h1
  refine Finset.sum_nbij' (fun x : ℕ × ℕ => (x.1, x.2 / p)) (fun y : ℕ × ℕ => (y.1, p * y.2))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨hD, hnd⟩ := hx
    have hD' := hD
    rw [Nat.mem_divisorsAntidiagonal] at hD'
    have key : p * (x.2 / p) = x.2 := Nat.mul_div_cancel' (hx2 x hD hnd)
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, ?_⟩, hnd⟩
    · apply Nat.eq_of_mul_eq_mul_left hp.pos
      calc p * (x.1 * (x.2 / p)) = x.1 * (p * (x.2 / p)) := by ring
        _ = x.1 * x.2 := by rw [key]
        _ = p * m := hD'.1
    · intro h0
      apply hD'.2
      rw [h0, mul_zero]
  · intro y hy
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hy
    obtain ⟨⟨hmul, hne⟩, hnd⟩ := hy
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, mul_ne_zero hp.ne_zero hne⟩, hnd⟩
    calc y.1 * (p * y.2) = p * (y.1 * y.2) := by ring
      _ = p * m := by rw [hmul]
  · intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨hD, hnd⟩ := hx
    show (x.1, p * (x.2 / p)) = x
    exact Prod.ext rfl (Nat.mul_div_cancel' (hx2 x hD hnd))
  · intro y _
    show (y.1, p * y.2 / p) = y
    exact Prod.ext rfl (Nat.mul_div_cancel_left y.2 hp.pos)
  · intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨hD, hnd⟩ := hx
    show hkTerm k c x N = hkTerm k c (x.1, p * (x.2 / p)) N
    rw [Nat.mul_div_cancel' (hx2 x hD hnd)]

/-- Splitting the divisor pairs of `p * m` by whether `p` divides the first entry. -/
theorem sum_divisorsAntidiagonal_mul_prime (k : ℤ) (c : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (m N : ℕ) :
    ∑ x ∈ Nat.divisorsAntidiagonal (p * m), hkTerm k c x N =
      ∑ y ∈ Nat.divisorsAntidiagonal m, hkTerm k c (p * y.1, y.2) N +
        ∑ y ∈ (Nat.divisorsAntidiagonal m).filter (fun y : ℕ × ℕ => ¬ p ∣ y.1),
          hkTerm k c (y.1, p * y.2) N := by
  rw [← sum_filter_dvd_mul k c hp m N, ← sum_filter_not_dvd_mul k c hp m N]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The prime composition identity (L1). -/
theorem compositeCoeff_mul_prime (k : ℤ) (c : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (m N : ℕ) :
    compositeCoeff k m c (p * N) +
        (if p ∣ N then (p : ℂ) ^ (k - 1) * compositeCoeff k m c (N / p) else 0) =
      compositeCoeff k (p * m) c N +
        (if p ∣ m then (p : ℂ) ^ (k - 1) * compositeCoeff k (m / p) c N else 0) := by
  have hA : compositeCoeff k (p * m) c N =
      ∑ y ∈ Nat.divisorsAntidiagonal m, hkTerm k c (p * y.1, y.2) N +
        ∑ y ∈ (Nat.divisorsAntidiagonal m).filter (fun y : ℕ × ℕ => ¬ p ∣ y.1),
          hkTerm k c (y.1, p * y.2) N := by
    rw [compositeCoeff_eq_sum]
    exact sum_divisorsAntidiagonal_mul_prime k c hp m N
  have hfirst := sum_hkTerm_mul_left k c hp m N
  have hB : compositeCoeff k m c (p * N) =
      ∑ y ∈ (Nat.divisorsAntidiagonal m).filter (fun y : ℕ × ℕ => p ∣ y.1),
          hkTerm k c y (p * N) +
        ∑ y ∈ (Nat.divisorsAntidiagonal m).filter (fun y : ℕ × ℕ => ¬ p ∣ y.1),
          hkTerm k c (y.1, p * y.2) N := by
    rw [compositeCoeff_eq_sum,
      ← Finset.sum_filter_add_sum_filter_not (Nat.divisorsAntidiagonal m)
        (fun y : ℕ × ℕ => p ∣ y.1) (fun y => hkTerm k c y (p * N))]
    congr 1
    exact Finset.sum_congr rfl
      (fun y hy => hkTerm_mul_right_of_not_dvd k c hp y (Finset.mem_filter.mp hy).2 N)
  have hC : ∑ y ∈ (Nat.divisorsAntidiagonal m).filter (fun y : ℕ × ℕ => p ∣ y.1),
        hkTerm k c y (p * N) =
      if p ∣ m then (p : ℂ) ^ (k - 1) * compositeCoeff k (m / p) c N else 0 := by
    by_cases hpm : p ∣ m
    · obtain ⟨m', rfl⟩ := hpm
      rw [Nat.mul_div_cancel_left m' hp.pos, ite_eq_left (dvd_mul_right p m'),
        sum_filter_dvd_mul k c hp m' (p * N)]
      have h2 : ∑ y ∈ Nat.divisorsAntidiagonal m', hkTerm k c (p * y.1, y.2) (p * N) =
          ∑ y ∈ Nat.divisorsAntidiagonal m', (p : ℂ) ^ (k - 1) * hkTerm k c y N :=
        Finset.sum_congr rfl (fun y _ => hkTerm_mul_mul k c hp y N)
      rw [h2, ← Finset.mul_sum, compositeCoeff_eq_sum]
    · rw [ite_eq_right hpm]
      apply Finset.sum_eq_zero
      intro y hy
      exfalso
      have hyD := (Finset.mem_filter.mp hy).1
      have hpy := (Finset.mem_filter.mp hy).2
      have hmul := (Nat.mem_divisorsAntidiagonal.mp hyD).1
      exact hpm (dvd_trans hpy (Dvd.intro y.2 hmul))
  rw [hB, hC, hA, hfirst]
  ring

/-- Strong induction (L2): if the coefficients `c` satisfy the prime relations, then
`compositeCoeff m c N = c m * c N` for all `m`, `N`. -/
theorem compositeCoeff_eq_mul (k : ℤ) (c : ℕ → ℂ) (h0 : c 0 = 0) (h1 : c 1 = 1)
    (hrel : ∀ p : ℕ, p.Prime → ∀ x : ℕ,
      c p * c x = c (p * x) + (if p ∣ x then (p : ℂ) ^ (k - 1) * c (x / p) else 0)) :
    ∀ m : ℕ, ∀ N : ℕ, compositeCoeff k m c N = c m * c N := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro N
    rcases Nat.lt_or_ge m 2 with hsmall | hbig
    · interval_cases m
      · simp [compositeCoeff, h0]
      · simp [compositeCoeff, h1]
    · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
      obtain ⟨m', rfl⟩ := hpm
      have hm'pos : 0 < m' := Nat.pos_of_ne_zero (fun h => by simp [h] at hbig)
      have hlt1 : m' < p * m' := by nlinarith [hp.two_le]
      have hlt2 : m' / p < p * m' := lt_of_le_of_lt (Nat.div_le_self m' p) hlt1
      have L := compositeCoeff_mul_prime k c hp m' N
      rw [ih m' hlt1 (p * N), ih m' hlt1 (N / p), ih (m' / p) hlt2 N] at L
      have hr1 := hrel p hp N
      have hr2 := hrel p hp m'
      split_ifs at L hr1 hr2 <;>
        linear_combination (-1 : ℂ) * L + (-c m') * hr1 + (c N) * hr2

/-- Pointwise matching of one pair of divisor pairs `x ∈ D(m)`, `y ∈ D(n)` (coprime `m, n`). -/
theorem term_pair (k : ℤ) (c : ℕ → ℂ) {m n : ℕ} (hm : 0 < m) (hmn : Nat.Coprime m n)
    (x y : ℕ × ℕ) (hx : x ∈ Nat.divisorsAntidiagonal m) (hy : y ∈ Nat.divisorsAntidiagonal n)
    (N : ℕ) :
    (if x.1 ∣ N then (x.1 : ℂ) ^ (k - 1) * hkTerm k c y (x.2 * (N / x.1)) else 0) =
      hkTerm k c (x.1 * y.1, x.2 * y.2) N := by
  rw [Nat.mem_divisorsAntidiagonal] at hx hy
  obtain ⟨hxm, hx2⟩ := hx
  obtain ⟨hyn, hy2⟩ := hy
  have hx1m : x.1 ∣ m := Dvd.intro _ hxm
  have hy1n : y.1 ∣ n := Dvd.intro _ hyn
  have hx2m : x.2 ∣ m := Dvd.intro_left _ hxm
  have hxpos : 0 < x.1 := Nat.pos_of_ne_zero (fun h0 => hm.ne' (by rw [← hxm, h0, zero_mul]))
  have hcop : Nat.Coprime y.1 x.2 :=
    Nat.Coprime.coprime_dvd_left hy1n (Nat.Coprime.coprime_dvd_right hx2m hmn.symm)
  by_cases hx1 : x.1 ∣ N
  · rw [ite_eq_left hx1]
    unfold hkTerm
    dsimp only
    by_cases hy1 : y.1 ∣ x.2 * (N / x.1)
    · have hN' : y.1 ∣ N / x.1 := (Nat.Coprime.dvd_mul_left hcop).mp hy1
      have hdiv : x.1 * y.1 ∣ N := by
        have := mul_dvd_mul_left x.1 hN'
        rwa [Nat.mul_div_cancel' hx1] at this
      rw [ite_eq_left hy1, ite_eq_left hdiv, ← Nat.div_div_eq_div_mul N x.1 y.1, Nat.mul_div_assoc x.2 hN']
      have harg : y.2 * (x.2 * (N / x.1 / y.1)) = x.2 * y.2 * (N / x.1 / y.1) := by ring
      rw [harg]
      push_cast
      rw [mul_zpow]
      ring
    · have hnd : ¬ x.1 * y.1 ∣ N := by
        intro h
        apply hy1
        have h' : x.1 * y.1 ∣ x.1 * (N / x.1) := by rwa [Nat.mul_div_cancel' hx1]
        have hN' : y.1 ∣ N / x.1 := Nat.dvd_of_mul_dvd_mul_left hxpos h'
        exact dvd_mul_of_dvd_right hN' x.2
      rw [ite_eq_right hy1, mul_zero, ite_eq_right hnd]
  · unfold hkTerm
    dsimp only
    rw [ite_eq_right hx1, ite_eq_right (fun h => hx1 (dvd_trans (dvd_mul_right x.1 y.1) h))]

/-- The coprime composition identity (L3) at the level of coefficients, for arbitrary `c`. -/
theorem compositeCoeff_comp_coprime (k : ℤ) (c : ℕ → ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) (N : ℕ) :
    compositeCoeff k m (compositeCoeff k n c) N = compositeCoeff k (m * n) c N := by
  have hL : compositeCoeff k m (compositeCoeff k n c) N =
      ∑ x ∈ Nat.divisorsAntidiagonal m, ∑ y ∈ Nat.divisorsAntidiagonal n,
        (if x.1 ∣ N then (x.1 : ℂ) ^ (k - 1) * hkTerm k c y (x.2 * (N / x.1)) else 0) := by
    rw [compositeCoeff_eq_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx1 : x.1 ∣ N
    · simp only [hkTerm, ite_eq_left hx1, compositeCoeff_eq_sum, Finset.mul_sum]
    · simp only [hkTerm, ite_eq_right hx1, Finset.sum_const_zero]
  rw [hL, ← Finset.sum_product', compositeCoeff_eq_sum]
  refine Finset.sum_nbij'
    (fun p : (ℕ × ℕ) × (ℕ × ℕ) => (p.1.1 * p.2.1, p.1.2 * p.2.2))
    (fun z : ℕ × ℕ => ((Nat.gcd z.1 m, m / Nat.gcd z.1 m), (Nat.gcd z.1 n, n / Nat.gcd z.1 n)))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hx, hy⟩ := hp
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, mul_ne_zero hx.2 hy.2⟩
    show p.1.1 * p.2.1 * (p.1.2 * p.2.2) = m * n
    calc p.1.1 * p.2.1 * (p.1.2 * p.2.2) = (p.1.1 * p.1.2) * (p.2.1 * p.2.2) := by ring
      _ = m * n := by rw [hx.1, hy.1]
  · intro z hz
    rw [Nat.mem_divisorsAntidiagonal] at hz
    obtain ⟨hzmn, hz2⟩ := hz
    have hg : Nat.gcd z.1 m ∣ m := Nat.gcd_dvd_right _ _
    have hgn : Nat.gcd z.1 n ∣ n := Nat.gcd_dvd_right _ _
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨Nat.mul_div_cancel' hg, hm.ne'⟩
    · rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨Nat.mul_div_cancel' hgn, hn.ne'⟩
  · intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hx, hy⟩ := hp
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    obtain ⟨hxm, hx2⟩ := hx
    obtain ⟨hyn, hy2⟩ := hy
    have hx1m : p.1.1 ∣ m := Dvd.intro _ hxm
    have hy1n : p.2.1 ∣ n := Dvd.intro _ hyn
    have hxpos : 0 < p.1.1 := Nat.pos_of_ne_zero (fun h0 => hm.ne' (by rw [← hxm, h0, zero_mul]))
    have hypos : 0 < p.2.1 := Nat.pos_of_ne_zero (fun h0 => hn.ne' (by rw [← hyn, h0, zero_mul]))
    have hym : Nat.Coprime p.2.1 m := Nat.Coprime.coprime_dvd_left hy1n hmn.symm
    have hxn : Nat.Coprime p.1.1 n := Nat.Coprime.coprime_dvd_left hx1m hmn
    have g1 : Nat.gcd (p.1.1 * p.2.1) m = p.1.1 := by
      rw [Nat.Coprime.gcd_mul_right_cancel p.1.1 hym, Nat.gcd_eq_left hx1m]
    have g2 : Nat.gcd (p.1.1 * p.2.1) n = p.2.1 := by
      rw [Nat.Coprime.gcd_mul_left_cancel p.2.1 hxn, Nat.gcd_eq_left hy1n]
    have q1 : m / p.1.1 = p.1.2 := by rw [← hxm, Nat.mul_div_cancel_left _ hxpos]
    have q2 : n / p.2.1 = p.2.2 := by rw [← hyn, Nat.mul_div_cancel_left _ hypos]
    show ((Nat.gcd (p.1.1 * p.2.1) m, m / Nat.gcd (p.1.1 * p.2.1) m),
      (Nat.gcd (p.1.1 * p.2.1) n, n / Nat.gcd (p.1.1 * p.2.1) n)) = p
    rw [g1, g2, q1, q2]
  · intro z hz
    rw [Nat.mem_divisorsAntidiagonal] at hz
    obtain ⟨hzmn, hz2⟩ := hz
    have hzpos : 0 < z.1 :=
      Nat.pos_of_ne_zero (fun h0 => (mul_ne_zero hm.ne' hn.ne') (by rw [← hzmn, h0, zero_mul]))
    have h1 : Nat.gcd z.1 m * Nat.gcd z.1 n = z.1 := by
      rw [← Nat.Coprime.gcd_mul z.1 hmn]
      exact Nat.gcd_eq_left (Dvd.intro _ hzmn)
    have h2 : m / Nat.gcd z.1 m * (n / Nat.gcd z.1 n) = z.2 := by
      rw [Nat.div_mul_div_comm (Nat.gcd_dvd_right z.1 m) (Nat.gcd_dvd_right z.1 n), h1, ← hzmn,
        Nat.mul_div_cancel_left _ hzpos]
    show (Nat.gcd z.1 m * Nat.gcd z.1 n, m / Nat.gcd z.1 m * (n / Nat.gcd z.1 n)) = z
    exact Prod.ext h1 h2
  · intro p hp
    rw [Finset.mem_product] at hp
    exact term_pair k c hm hmn p.1 p.2 hp.1 hp.2 N

end TernaryPeriodPolynomials.Argument.Identities
