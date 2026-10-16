module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtDictionary

@[expose] public section


/-!
# Injectivity of `t ↦ L_t` on the Hermite triples of level `p^s`

Formalized by Claude Haiku 5.5.

For a Hermite triple `t = (a, b, d)` with `0 < a`, `a d = p^s`, `b < d`, the lattice
`L_t = hermLat p t` determines `t`:
* `(0, y) ∈ L_t ↔ d ∣ y` (since `a ≠ 0`), so `d` is determined;
* `a` is determined by `a d = p^s`;
* `b` is determined by `b < d` and `(b, a) ∈ L_t`.
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp (Mz mulLin mulLin_apply)
open TernaryPeriodPolynomials.Argument.LatticeCounts (hnfData mem_hnfData)

variable {p : ℕ} [hp : Fact p.Prime]

/-- `p^i` divides a natural number in `ℤ_p` iff it does in `ℕ`. -/
theorem pow_dvd_natCast_iff' (i n : ℕ) : (p : ℤ_[p]) ^ i ∣ (n : ℤ_[p]) ↔ p ^ i ∣ n := by
  have h1 : (n : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ i} ↔ (p : ℤ_[p]) ^ i ∣ (n : ℤ_[p]) :=
    Ideal.mem_span_singleton
  rw [← h1, ← ker_toZModPow, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff]

/-- Membership of `(0, y)` in `L_t` for `t = (a, b, d)` with `a ≠ 0`. -/
theorem mem_hermLat_fst_zero {a b d : ℕ} (ha : a ≠ 0) (y : ℤ_[p]) :
    ((0 : ℤ_[p]), y) ∈ hermLat p (a, b, d) ↔ (d : ℤ_[p]) ∣ y := by
  rw [hermLat, LinearMap.mem_range]
  have ha' : (a : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr ha
  constructor
  · rintro ⟨x, hx⟩
    have h1 := congrArg Prod.fst hx
    have h2 := congrArg Prod.snd hx
    simp only [mulLin_apply, Mz] at h1 h2
    have hx1 : x.1 = 0 := by
      have h1' : (a : ℤ_[p]) * x.1 = 0 := by simpa using h1
      exact (mul_eq_zero.mp h1').resolve_left ha'
    refine ⟨x.2, ?_⟩
    rw [hx1] at h2
    simp at h2
    rw [← h2]
  · intro hd
    obtain ⟨c, hc⟩ := hd
    refine ⟨(0, c), ?_⟩
    rw [hc]
    ext <;> simp [mulLin_apply, Mz]

/-- Divisibility by `p^i` between naturals below `p^i` forces equality. -/
theorem eq_of_dvd_sub {i b b' : ℕ} (hb : b < p ^ i) (hb' : b' < p ^ i)
    (h : (p : ℤ_[p]) ^ i ∣ (b : ℤ_[p]) - (b' : ℤ_[p])) : b = b' := by
  rcases le_total b' b with hle | hle
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hle
    push_cast at h
    have h2 : (p : ℤ_[p]) ^ i ∣ (n : ℤ_[p]) := by simpa using h
    have h3 : p ^ i ∣ n := (pow_dvd_natCast_iff' i n).1 h2
    have hn : n = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hle
    push_cast at h
    have h2 : (p : ℤ_[p]) ^ i ∣ (n : ℤ_[p]) := by
      have := dvd_neg.2 h
      simpa using this
    have h3 : p ^ i ∣ n := (pow_dvd_natCast_iff' i n).1 h2
    have hn : n = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega

/-- **Injectivity.** `t ↦ hermLat p t` is injective on the Hermite triples of level `p^s`. -/
theorem hermLat_inj {s : ℕ} {t t' : ℕ × ℕ × ℕ} (ht : t ∈ hnfData (p ^ s))
    (ht' : t' ∈ hnfData (p ^ s)) (h : hermLat p t = hermLat p t') : t = t' := by
  obtain ⟨a, b, d⟩ := t
  obtain ⟨a', b', d'⟩ := t'
  have hpos : 0 < p ^ s := pow_pos hp.out.pos s
  obtain ⟨ha, hdet, hbd⟩ : 0 < a ∧ a * d = p ^ s ∧ b < d :=
    (mem_hnfData hpos _).1 ht
  obtain ⟨ha', hdet', hbd'⟩ : 0 < a' ∧ a' * d' = p ^ s ∧ b' < d' :=
    (mem_hnfData hpos _).1 ht'
  have ha0 : a ≠ 0 := by omega
  have ha0' : a' ≠ 0 := by omega
  -- `d` and `d'` divide each other in `ℤ_p`
  have k1 : (d : ℤ_[p]) ∣ (d' : ℤ_[p]) := by
    have m1 : ((0 : ℤ_[p]), (d' : ℤ_[p])) ∈ hermLat p (a', b', d') :=
      (mem_hermLat_fst_zero ha0' (d' : ℤ_[p])).2 dvd_rfl
    rw [← h] at m1
    exact (mem_hermLat_fst_zero ha0 (d' : ℤ_[p])).1 m1
  have k2 : (d' : ℤ_[p]) ∣ (d : ℤ_[p]) := by
    have m1 : ((0 : ℤ_[p]), (d : ℤ_[p])) ∈ hermLat p (a, b, d) :=
      (mem_hermLat_fst_zero ha0 (d : ℤ_[p])).2 dvd_rfl
    rw [h] at m1
    exact (mem_hermLat_fst_zero ha0' (d : ℤ_[p])).1 m1
  -- both are powers of `p`
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1 (Dvd.intro_left a hdet)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (Dvd.intro_left a' hdet')
  have k1' : p ^ i ∣ p ^ j := by
    have e : (d : ℤ_[p]) ∣ (d' : ℤ_[p]) := k1
    rw [hi, hj] at e
    exact (pow_dvd_natCast_iff' i (p ^ j)).1 (by push_cast at e ⊢; exact e)
  have k2' : p ^ j ∣ p ^ i := by
    have e : (d' : ℤ_[p]) ∣ (d : ℤ_[p]) := k2
    rw [hi, hj] at e
    exact (pow_dvd_natCast_iff' j (p ^ i)).1 (by push_cast at e ⊢; exact e)
  have hdd : d = d' := by
    rw [hi, hj, Nat.dvd_antisymm k1' k2']
  subst hdd
  have haa : a = a' := by
    have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h0 => by
      rw [h0, mul_zero] at hdet
      exact absurd hdet.symm (ne_of_gt hpos))
    exact Nat.eq_of_mul_eq_mul_right hd0 (hdet.trans hdet'.symm)
  subst haa
  -- `b` is determined by `(a, b) ∈ L_t`
  have m2 : ((a : ℤ_[p]), (b : ℤ_[p])) ∈ hermLat p (a, b, d) :=
    ⟨(1, 0), by ext <;> simp [mulLin_apply, Mz]⟩
  rw [h, hermLat, LinearMap.mem_range] at m2
  obtain ⟨x, hx⟩ := m2
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only [mulLin_apply, Mz] at h1 h2
  have ha0c : (a : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  have hx1 : x.1 = 1 := by
    have h1' : (a : ℤ_[p]) * x.1 = (a : ℤ_[p]) * 1 := by simpa using h1
    exact mul_left_cancel₀ ha0c h1'
  rw [hx1] at h2
  have h2' : (b' : ℤ_[p]) + (d : ℤ_[p]) * x.2 = b := by simpa [Mz] using h2
  have hdc : (d : ℤ_[p]) = (p : ℤ_[p]) ^ i := by rw [hi, Nat.cast_pow]
  have hbb : b = b' := by
    refine eq_of_dvd_sub (p := p) (i := i) ?_ ?_ ?_
    · rw [← hi]; exact hbd
    · rw [← hi]; exact hbd'
    · refine ⟨x.2, ?_⟩
      linear_combination -h2' + x.2 * hdc
  subst hbb
  rfl

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
