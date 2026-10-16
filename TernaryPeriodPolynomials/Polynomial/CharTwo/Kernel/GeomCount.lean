module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.HilbertSeries
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GradedCount
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

@[expose] public section





noncomputable section

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open PowerSeries

/-- **STEP2b item (ii), step 0.** Rewrite a `PowerSeries.coeff_mul` antidiagonal sum as a
`Finset.range`-indexed sum, avoiding any need to reason about antidiagonal membership. -/
theorem coeff_mul_range (φ ψ : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (φ * ψ) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k φ * PowerSeries.coeff (n - k) ψ := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i φ * PowerSeries.coeff j ψ) n

/-- The number of `c ≤ N` with `c * w = m` is `1` if `w ∣ m` (and `m ≤ N`) and `0` otherwise. -/
theorem unaryCard (w m N : ℕ) (hw : 0 < w) (hmN : m ≤ N) :
    ((Finset.range (N + 1)).filter (fun c => c * w = m)).card = if w ∣ m then 1 else 0 := by
  by_cases h : w ∣ m
  · simp only [h, ite_true]
    obtain ⟨c, hc⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨c, Finset.ext fun x => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hxw⟩
      have hx : x * w = c * w := by rw [hxw, hc, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hw hx
    · intro hxc
      refine ⟨?_, by rw [hxc, hc, mul_comm]⟩
      have hcm : c ≤ m := by rw [hc]; exact Nat.le_mul_of_pos_left c hw
      omega
  · simp only [h, ite_false]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact h ⟨x, by rw [← hx.2, mul_comm]⟩

/-- **STEP2b item (ii), binary case.** The `m`-th coefficient of `geom u * geom v` equals the
number of pairs `(p,q)`, both bounded by an ambient `N ≥ m`, with `p*u+q*v=m`. The ambient bound
`N` is kept as a free parameter (rather than fixed to `m`) so this lemma can be reused, instantiated
at a larger `N`, inside the fiber computation of the triple case below. -/
theorem coeff_geom_mul_eq_card (u v m N : ℕ) (hu : 0 < u) (hv : 0 < v) (hmN : m ≤ N) :
    PowerSeries.coeff m (geom u * geom v) =
      ((((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
          (fun p => p.1 * u + p.2 * v = m)).card : ℤ) := by
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (if u ∣ k then (1 : ℤ) else 0) * (if v ∣ (m - k) then (1 : ℤ) else 0) =
        ((((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
          (fun p => p.1 * u = k ∧ p.2 * v = m - k)).card : ℤ) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hfp : (((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
        (fun p => p.1 * u = k ∧ p.2 * v = m - k)) =
        ((Finset.range (N + 1)).filter (fun a => a * u = k)) ×ˢ
        ((Finset.range (N + 1)).filter (fun b => b * v = m - k)) :=
      Finset.filter_product (fun a => a * u = k) (fun b => b * v = m - k)
    have hc : (((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
        (fun p => p.1 * u = k ∧ p.2 * v = m - k)).card =
        (if u ∣ k then 1 else 0) * (if v ∣ (m - k) then 1 else 0) := by
      rw [hfp, Finset.card_product,
        unaryCard u k N hu (by omega), unaryCard v (m - k) N hv (by omega)]
    rw [hc]
    split_ifs <;> norm_num
  have hfiber : (((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
      (fun p => p.1 * u + p.2 * v = m)).card =
      ∑ k ∈ Finset.range (m + 1),
        (((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
          (fun p => p.1 * u = k ∧ p.2 * v = m - k)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun p : ℕ × ℕ => p.1 * u) (t := Finset.range (m + 1))
      (by
        intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter] at hp
        obtain ⟨-, heq⟩ := hp
        simp only [Finset.mem_coe, Finset.mem_range]
        omega)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range] at hk
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro p _
    omega
  rw [coeff_mul_range]
  simp only [geom_coeff]
  rw [hfiber]
  push_cast
  exact Finset.sum_congr rfl hterm

/-- **STEP2b item (ii), triple case.** The `n`-th coefficient of `geom w0 * geom w1 * geom w2`
equals the number of triples `(p,q,r)` (associated as `(ℕ × ℕ) × ℕ`), each bounded by `n`, with
`p*w0+q*w1+r*w2=n`. -/
theorem coeff_geom_three_eq_card (w0 w1 w2 n : ℕ) (h0 : 0 < w0) (h1 : 0 < w1) (h2 : 0 < w2) :
    PowerSeries.coeff n (geom w0 * geom w1 * geom w2) =
      (((((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ (Finset.range (n + 1))).filter
          (fun t => t.1.1 * w0 + t.1.2 * w1 + t.2 * w2 = n)).card : ℤ) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      PowerSeries.coeff k (geom w0 * geom w1) * (if w2 ∣ (n - k) then (1 : ℤ) else 0) =
        (((((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ (Finset.range (n + 1))).filter
          (fun t => t.1.1 * w0 + t.1.2 * w1 = k ∧ t.2 * w2 = n - k)).card : ℤ) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hsplit : ((((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ (Finset.range (n + 1))).filter
        (fun t => t.1.1 * w0 + t.1.2 * w1 = k ∧ t.2 * w2 = n - k)) =
        (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
          (fun x => x.1 * w0 + x.2 * w1 = k)) ×ˢ
        ((Finset.range (n + 1)).filter (fun c => c * w2 = n - k)) :=
      Finset.filter_product (fun x : ℕ × ℕ => x.1 * w0 + x.2 * w1 = k) (fun c => c * w2 = n - k)
    rw [hsplit, Finset.card_product]
    push_cast
    rw [coeff_geom_mul_eq_card w0 w1 k n h0 h1 (by omega)]
    rw [unaryCard w2 (n - k) n h2 (by omega)]
    push_cast
    ring
  have hfiber : ((((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ (Finset.range (n + 1))).filter
      (fun t => t.1.1 * w0 + t.1.2 * w1 + t.2 * w2 = n)).card =
      ∑ k ∈ Finset.range (n + 1),
        (((((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ (Finset.range (n + 1))).filter
          (fun t => t.1.1 * w0 + t.1.2 * w1 = k ∧ t.2 * w2 = n - k)).card) := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun t : (ℕ × ℕ) × ℕ => t.1.1 * w0 + t.1.2 * w1) (t := Finset.range (n + 1))
      (by
        intro t ht
        simp only [Finset.mem_coe, Finset.mem_filter] at ht
        obtain ⟨-, heq⟩ := ht
        simp only [Finset.mem_coe, Finset.mem_range]
        omega)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range] at hk
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro t _
    omega
  rw [coeff_mul_range]
  simp only [geom_coeff]
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum, ← hfiber]

/-- Expand `Finsupp.weight` on `Fin 3 →₀ ℕ` into its three coordinates. -/
theorem weight_eq_triple_sum (w : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) :
    Finsupp.weight w d = d 0 * w 0 + d 1 * w 1 + d 2 * w 2 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp [Fin.sum_univ_three, smul_eq_mul]

/-- Hand-rolled total equivalence turning a finitely-supported function on `Fin 3` into an
explicit ℕ-triple (associated as `(ℕ × ℕ) × ℕ` to match `Finset.filter_product`'s shape). -/
def finsuppFin3Equiv : (Fin 3 →₀ ℕ) ≃ (ℕ × ℕ) × ℕ :=
  Finsupp.equivFunOnFinite.trans
    { toFun := fun x => ((x 0, x 1), x 2)
      invFun := fun t => ![t.1.1, t.1.2, t.2]
      left_inv := fun x => by funext i; fin_cases i <;> simp
      right_inv := fun t => by simp }

theorem finsuppFin3Equiv_apply (d : Fin 3 →₀ ℕ) :
    finsuppFin3Equiv d = ((d 0, d 1), d 2) := rfl

/-- **STEP2b item (ii), bridge.** `Nat.card` of the weight-`n` exponent vectors on `Fin 3`
equals the `n`-th triple-count Finset's cardinality. -/
theorem card_weight_three_eq_card (w : Fin 3 → ℕ) (n : ℕ)
    (h0 : 0 < w 0) (h1 : 0 < w 1) (h2 : 0 < w 2) :
    Nat.card {d : Fin 3 →₀ ℕ | Finsupp.weight w d = n} =
      (((((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ (Finset.range (n + 1))).filter
          (fun t => t.1.1 * w 0 + t.1.2 * w 1 + t.2 * w 2 = n)).card) := by
  have e1 : {d : Fin 3 →₀ ℕ | Finsupp.weight w d = n} ≃
      {t : (ℕ × ℕ) × ℕ | t.1.1 * w 0 + t.1.2 * w 1 + t.2 * w 2 = n} :=
    finsuppFin3Equiv.subtypeEquiv (fun d => by
      simp only [Set.mem_ofPred_eq]
      rw [finsuppFin3Equiv_apply, weight_eq_triple_sum])
  have hiff : ∀ t : (ℕ × ℕ) × ℕ, (t.1.1 * w 0 + t.1.2 * w 1 + t.2 * w 2 = n) ↔
      t ∈ (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ (Finset.range (n + 1))).filter
        (fun t => t.1.1 * w 0 + t.1.2 * w 1 + t.2 * w 2 = n) := by
    intro t
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · intro ht
      have hb0 : t.1.1 < n + 1 := by
        have hm : t.1.1 ≤ w 0 * t.1.1 := Nat.le_mul_of_pos_left t.1.1 h0
        rw [mul_comm] at hm; omega
      have hb1 : t.1.2 < n + 1 := by
        have hm : t.1.2 ≤ w 1 * t.1.2 := Nat.le_mul_of_pos_left t.1.2 h1
        rw [mul_comm] at hm; omega
      have hb2 : t.2 < n + 1 := by
        have hm : t.2 ≤ w 2 * t.2 := Nat.le_mul_of_pos_left t.2 h2
        rw [mul_comm] at hm; omega
      exact ⟨⟨⟨hb0, hb1⟩, hb2⟩, ht⟩
    · exact fun h => h.2
  rw [Nat.card_congr (e1.trans (Equiv.subtypeEquivRight hiff)), Nat.card_eq_finsetCard]

/-- **STEP2b item (ii), capstone.** The count of `Fin 3 →₀ ℕ` exponent vectors of weighted
degree `n` equals the `n`-th coefficient of `geom (w 0) * geom (w 1) * geom (w 2)`. This is the
bridge connecting `GradedCount.lean`'s `Nat.card`-based finrank statement to
`HilbertSeries.lean`'s `PowerSeries.coeff`-based generating-function identity. -/
theorem card_weight_eq_coeff (w : Fin 3 → ℕ) (n : ℕ)
    (h0 : 0 < w 0) (h1 : 0 < w 1) (h2 : 0 < w 2) :
    (Nat.card {d : Fin 3 →₀ ℕ | Finsupp.weight w d = n} : ℤ) =
      PowerSeries.coeff n (geom (w 0) * geom (w 1) * geom (w 2)) := by
  rw [card_weight_three_eq_card w n h0 h1 h2, coeff_geom_three_eq_card (w 0) (w 1) (w 2) n h0 h1 h2]

end TernaryPeriodPolynomials.Argument.CharTwoKernel
