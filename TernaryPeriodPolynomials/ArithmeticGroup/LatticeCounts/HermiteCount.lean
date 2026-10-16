module

public import Mathlib

@[expose] public section


/-!
# Hermite normal forms of index `p^r` sublattices of `ℤ²`: counts

Formalized by Claude Haiku 5.5.
Paper: Appendix C,
(the counting identity behind `eq:cyclic-hecke`: lattices of index `p^r` in `ℤ_p²`, cyclic ones
`ℤ_p²/Λ` cyclic, noncyclic ones `Λ = pΛ'` with `[ℤ_p² : Λ'] = p^(r-2)`).

Sublattices are described by their Hermite normal form: the row span `Λ = ⟨(a, b), (0, d)⟩ ⊆ ℤ²` of a
triple `(a, b, d)` of naturals with `a, d ≥ 1`, `a d = p^r` and `0 ≤ b < d`. The triples are the literal
object `hnfData (p^r)`. The bijection between finite-index sublattices and Hermite triples is the standard
fact and is NOT formalized here; all claims below are statements about the triples.
The quotient `ℤ²/Λ` is cyclic exactly when the Smith invariant `gcd(a, b, d)` equals `1`, which is the
predicate used for `cyclicHNF`.

Proved here (for every prime `p` and every `r`):
* `card_hnfData`: `#hnfData (p^r) = ∑_{i ≤ r} p^i`;
* `nonCyclicHNF_eq`: for `r ≥ 2` the noncyclic triples are exactly `p` times the triples of level `r-2`;
* `card_nonCyclicHNF`: `#noncyclic = ∑_{i < r-1} p^i = #hnfData (p^(r-2))`;
* `card_cyclicHNF`: for `r ≥ 1`, `#cyclic = p^r + p^(r-1)`.
-/

namespace TernaryPeriodPolynomials.Argument.LatticeCounts

open Finset

/-- Hermite normal form triples `(a, b, d)` with `a d = n`, `a ≥ 1`, `0 ≤ b < d`. -/
def hnfData (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1)) ×ˢ (range (n + 1))).filter
    fun t => 0 < t.1 ∧ t.1 * t.2.2 = n ∧ t.2.1 < t.2.2

/-- The cyclic Hermite triples: those with `gcd(a, b, d) = 1`. -/
def cyclicHNF (p r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (hnfData (p ^ r)).filter fun t => Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1

/-- The noncyclic Hermite triples: those with `gcd(a, b, d) ≠ 1`. -/
def nonCyclicHNF (p r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (hnfData (p ^ r)).filter fun t => ¬ Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1

theorem mem_hnfData {n : ℕ} (hn : 0 < n) (t : ℕ × ℕ × ℕ) :
    t ∈ hnfData n ↔ 0 < t.1 ∧ t.1 * t.2.2 = n ∧ t.2.1 < t.2.2 := by
  unfold hnfData
  simp only [mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2, h3⟩
    have hd1 : t.1 ≤ n := Nat.le_of_dvd hn ⟨t.2.2, h2.symm⟩
    have hd2 : t.2.2 ≤ n := Nat.le_of_dvd hn ⟨t.1, by rw [mul_comm]; exact h2.symm⟩
    exact ⟨⟨by omega, by omega, by omega⟩, h1, h2, h3⟩


theorem card_fiber {n a : ℕ} (hn : 0 < n) (ha : a ∈ n.divisors) :
    ((hnfData n).filter fun t => t.1 = a).card = n / a := by
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
  obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors ha
  have hdiv : n / a = c := by rw [hc, Nat.mul_div_cancel_left c ha0]
  have hinj : Function.Injective (fun b : ℕ => ((a, b, n / a) : ℕ × ℕ × ℕ)) := by
    intro x y h
    simpa using h
  rw [← Finset.card_range (n / a), ← Finset.card_image_of_injective _ hinj]
  congr 1
  ext t
  simp only [mem_filter, mem_image, mem_range, mem_hnfData hn]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    rw [h4] at h2
    have ht : t.2.2 = n / a := by
      rw [← h2, Nat.mul_div_cancel_left _ ha0]
    refine ⟨t.2.1, by omega, ?_⟩
    exact Prod.ext h4.symm (Prod.ext rfl ht.symm)
  · rintro ⟨b, hb, rfl⟩
    refine ⟨⟨ha0, ?_, hb⟩, rfl⟩
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)

theorem card_hnfData {p r : ℕ} [Fact p.Prime] :
    (hnfData (p ^ r)).card = ∑ i ∈ range (r + 1), p ^ i := by
  have hn : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  have hmaps : Set.MapsTo (fun t : ℕ × ℕ × ℕ => t.1) (hnfData (p ^ r) : Set (ℕ × ℕ × ℕ))
      ((p ^ r).divisors : Set ℕ) := by
    intro t ht
    rw [Finset.mem_coe, mem_hnfData hn] at ht
    rw [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨⟨t.2.2, ht.2.1.symm⟩, hn.ne'⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  rw [Finset.sum_congr rfl (fun a ha => card_fiber hn ha)]
  have hsum := Nat.sum_div_divisors (p ^ r) (fun d => d)
  rw [hsum, Nat.sum_divisors_prime_pow Fact.out]


/-- A triple `(a, b, d)` with `a d = p^r` has `gcd(a, b, d) ≠ 1` exactly when `p` divides `a`, `b` and `d`. -/
theorem gcd_ne_one_iff {p r a b d : ℕ} [hp : Fact p.Prime] (h : a * d = p ^ r) :
    ¬ Nat.gcd (Nat.gcd a b) d = 1 ↔ p ∣ a ∧ p ∣ b ∧ p ∣ d := by
  constructor
  · intro hg
    have hq : (Nat.gcd (Nat.gcd a b) d).minFac.Prime := Nat.minFac_prime hg
    have hqg : (Nat.gcd (Nat.gcd a b) d).minFac ∣ Nat.gcd (Nat.gcd a b) d := Nat.minFac_dvd _
    have hqa : (Nat.gcd (Nat.gcd a b) d).minFac ∣ a :=
      (hqg.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_left a b)
    have hqb : (Nat.gcd (Nat.gcd a b) d).minFac ∣ b :=
      (hqg.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_right a b)
    have hqd : (Nat.gcd (Nat.gcd a b) d).minFac ∣ d := hqg.trans (Nat.gcd_dvd_right _ d)
    have hqp : (Nat.gcd (Nat.gcd a b) d).minFac = p := by
      have hdvd : (Nat.gcd (Nat.gcd a b) d).minFac ∣ p ^ r := by
        rw [← h]
        exact dvd_mul_of_dvd_left hqa d
      exact (Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).1 (hq.dvd_of_dvd_pow hdvd)
    rw [hqp] at hqa hqb hqd
    exact ⟨hqa, hqb, hqd⟩
  · rintro ⟨ha, hb, hd⟩ hg
    have : p ∣ Nat.gcd (Nat.gcd a b) d := Nat.dvd_gcd (Nat.dvd_gcd ha hb) hd
    rw [hg] at this
    exact (Fact.out : p.Prime).not_dvd_one this

/-- Scaling a Hermite triple by `p`. -/
def scaleHNF (p : ℕ) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (p * t.1, p * t.2.1, p * t.2.2)

theorem scaleHNF_injective {p : ℕ} (hp : p ≠ 0) : Function.Injective (scaleHNF p) := by
  rintro ⟨a, b, d⟩ ⟨a', b', d'⟩ h
  simp only [scaleHNF, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [Nat.mul_left_cancel_iff (Nat.pos_of_ne_zero hp) |>.mp h1,
    Nat.mul_left_cancel_iff (Nat.pos_of_ne_zero hp) |>.mp h2,
    Nat.mul_left_cancel_iff (Nat.pos_of_ne_zero hp) |>.mp h3]

/-- The noncyclic Hermite triples of index `p^r`, `r ≥ 2`, are exactly `p` times the Hermite triples of index `p^(r-2)`. -/
theorem nonCyclicHNF_eq {p r : ℕ} [hp : Fact p.Prime] (hr : 2 ≤ r) :
    nonCyclicHNF p r = (hnfData (p ^ (r - 2))).image (scaleHNF p) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpow : p ^ r = p ^ 2 * p ^ (r - 2) := by
    rw [← pow_add, show 2 + (r - 2) = r by omega]
  ext ⟨a, b, d⟩
  constructor
  · intro ht
    unfold nonCyclicHNF at ht
    rw [mem_filter, mem_hnfData (pow_pos hp0 r)] at ht
    obtain ⟨⟨ha, h, hbd⟩, hg⟩ := ht
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨d', rfl⟩⟩ := (gcd_ne_one_iff h).1 hg
    have ha' : 0 < a' := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
    have hkey : a' * d' = p ^ (r - 2) := by
      have h2 : p ^ 2 * (a' * d') = p ^ 2 * p ^ (r - 2) := by
        rw [← hpow, ← h]
        ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h2
    have hb'd' : b' < d' := Nat.lt_of_mul_lt_mul_left hbd
    rw [Finset.mem_image]
    refine ⟨(a', b', d'), ?_, rfl⟩
    rw [mem_hnfData (pow_pos hp0 (r - 2))]
    exact ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at ha'), hkey, hb'd'⟩
  · intro ht
    rw [Finset.mem_image] at ht
    obtain ⟨⟨a', b', d'⟩, hs, hst⟩ := ht
    rw [mem_hnfData (pow_pos hp0 (r - 2))] at hs
    simp only [scaleHNF, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl, rfl⟩ := hst
    unfold nonCyclicHNF
    rw [mem_filter, mem_hnfData (pow_pos hp0 r)]
    obtain ⟨hs1, hs2, hs3⟩ := hs
    have hmul : p * a' * (p * d') = p ^ r := by
      rw [hpow]
      calc p * a' * (p * d') = p ^ 2 * (a' * d') := by ring
        _ = p ^ 2 * p ^ (r - 2) := by rw [hs2]
    refine ⟨⟨Nat.mul_pos hp0 hs1, hmul, Nat.mul_lt_mul_of_pos_left hs3 hp0⟩, ?_⟩
    exact (gcd_ne_one_iff hmul).2 ⟨dvd_mul_right p a', dvd_mul_right p b', dvd_mul_right p d'⟩

theorem card_nonCyclicHNF {p r : ℕ} [hp : Fact p.Prime] (hr : 2 ≤ r) :
    (nonCyclicHNF p r).card = ∑ i ∈ range (r - 1), p ^ i := by
  rw [nonCyclicHNF_eq hr, card_image_of_injective _ (scaleHNF_injective (Fact.out : p.Prime).ne_zero),
    card_hnfData]
  rw [show r - 1 = r - 2 + 1 by omega]

theorem card_cyclicHNF_one {p : ℕ} [hp : Fact p.Prime] : (nonCyclicHNF p 1).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  rintro ⟨a, b, d⟩ ht
  unfold nonCyclicHNF at ht
  rw [mem_filter, mem_hnfData (pow_pos (Fact.out : p.Prime).pos 1)] at ht
  obtain ⟨⟨-, h, -⟩, hg⟩ := ht
  obtain ⟨ha, -, hd⟩ := (gcd_ne_one_iff h).1 hg
  have hdvd : p * p ∣ p ^ 1 := by
    rw [← h]
    exact Nat.mul_dvd_mul ha hd
  have hle := Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos 1) hdvd
  have h2 := (Fact.out : p.Prime).two_le
  rw [pow_one] at hle
  nlinarith

theorem card_cyclicHNF {p r : ℕ} [hp : Fact p.Prime] (hr : 1 ≤ r) :
    (cyclicHNF p r).card = p ^ r + p ^ (r - 1) := by
  have hsplit : (cyclicHNF p r).card + (nonCyclicHNF p r).card = (hnfData (p ^ r)).card :=
    card_filter_add_card_filter_not _
  rw [card_hnfData] at hsplit
  rcases Nat.lt_or_ge r 2 with hlt | hge
  · obtain rfl : r = 1 := by omega
    rw [card_cyclicHNF_one] at hsplit
    norm_num [Finset.sum_range_succ] at hsplit ⊢
    omega
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
    have e : s + 2 - 1 = s + 1 := by omega
    rw [card_nonCyclicHNF hge, e, sum_range_succ (fun i => p ^ i) (s + 2),
      sum_range_succ (fun i => p ^ i) (s + 1)] at hsplit
    rw [e]
    omega


/-- Noncyclic lattices of index `p^r` are in bijection with lattices of index `p^(r-2)`: `#noncyclic = #hnfData (p^(r-2))`. -/
theorem card_nonCyclicHNF_eq_hnfData {p r : ℕ} [hp : Fact p.Prime] (hr : 2 ≤ r) :
    (nonCyclicHNF p r).card = (hnfData (p ^ (r - 2))).card := by
  rw [nonCyclicHNF_eq hr, card_image_of_injective _ (scaleHNF_injective (Fact.out : p.Prime).ne_zero)]

end TernaryPeriodPolynomials.Argument.LatticeCounts
