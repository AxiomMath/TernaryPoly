module

public import TernaryPeriodPolynomials.PeriodPolynomial.Lift.JetRecovery
public import TernaryPeriodPolynomials.SymmetricSolution.BinaryPeriodLift
public import TernaryPeriodPolynomials.SymmetricSolution.PeriodTower

@[expose] public section


/-!
# Uniqueness of the symmetric period towers (Lemma 2.3 and Corollary 2.4)

Lemma 2.3 (`lem:period-extraction`) of the paper
asserts that an odd-degree symmetric `v` with `J_v = 0` lies in `⊕_{j ≥ 0} w^{2j} L(𝓑_{m+1-2j})`,
that every lift is polynomial, and that the expression is unique; Corollary 2.4
(`cor:period-towers`) asserts the same uniqueness for the towers `f = ∑ w^{e_j} Φ(q_j)`.
Existence is `TernaryPoly.symmetric_odd_period_tower` / `TernaryPoly.symmetric_even_period_tower`;
this module proves the uniqueness, by the paper's argument: the first-plane data
`v ↦ (∂₁ + ∂₂) v` restricted to `w = 0` vanishes on `w² u` and recovers the rotated mixed
derivative of `q` from `L(q)`, which determines `q`.

Here `w = x + y + z`, a tower is a finite family `(q_i, l_i)` of symmetric binary periods `q_i`
(`SymmetricBinaryPeriodRelations`) with polynomial lifts `Φ(q_i) = w l_i`, and families are
compared after extension by zero.

Written by Claude Opus 5.5. The private lemmas
`bind_chain_rule` and `binaryBoundary_binaryLiftEval'` repeat private lemmas of
`TernaryPeriodPolynomials/PeriodPolynomial/Lift/JetRecovery.lean` (same statements and proofs).
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.PeriodTowers

open TernaryPoly

local notation "BP" => MvPolynomial (Fin 2) ℚ

/-- The coordinate sum `w = x + y + z`. -/
local notation "W" => (X 0 + X 1 + X 2 : TernaryPolynomial)

private theorem bind_chain_rule {σ : Type*} (q : BP) (a b : MvPolynomial σ ℚ) (i : σ) :
    pderiv i (bind₁ ![a, b] q) = bind₁ ![a, b] (pderiv 0 q) * pderiv i a +
      bind₁ ![a, b] (pderiv 1 q) * pderiv i b := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p j hp => fin_cases j <;> simp [map_mul, map_add, hp] <;> ring

private theorem binaryBoundary_binaryLiftEval' (q : BP) :
    binaryBoundary (binaryLiftEval q (X 0) (X 1)) = bind₁ ![-X 1, X 0] q := by
  simp only [binaryBoundary, binaryLiftEval, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The first-plane data of a ternary polynomial: `(∂₁ + ∂₂) v` restricted to `w = 0`. -/
def firstPlaneData (v : TernaryPolynomial) : BP := binaryBoundary (pderiv 0 v + pderiv 1 v)

theorem firstPlaneData_add (u v : TernaryPolynomial) :
    firstPlaneData (u + v) = firstPlaneData u + firstPlaneData v := by
  simp only [firstPlaneData, binaryBoundary, map_add]
  ring

theorem firstPlaneData_zero : firstPlaneData 0 = 0 := by
  simp [firstPlaneData, binaryBoundary]

private theorem binaryBoundary_W : binaryBoundary W = 0 := by
  simp [binaryBoundary]

/-- The first-plane data vanish on multiples of `w²`. -/
theorem firstPlaneData_W_sq_mul (u : TernaryPolynomial) : firstPlaneData (W ^ 2 * u) = 0 := by
  have h : pderiv 0 (W ^ 2 * u) + pderiv 1 (W ^ 2 * u) =
      W * (2 * u + W * pderiv 0 u + (2 * u + W * pderiv 1 u)) := by
    simp
    ring
  rw [firstPlaneData, h]
  have hW := binaryBoundary_W
  simp only [binaryBoundary] at hW ⊢
  rw [map_mul, hW, zero_mul]

/-- The first-plane data of a polynomial lift `L(q)` is the rotated mixed derivative of `q`. -/
theorem firstPlaneData_lift {q : BP} {l : TernaryPolynomial}
    (hl : binaryPeriodLift q = W * l) :
    firstPlaneData l = bind₁ ![-X 1, X 0] (pderiv 0 (pderiv 1 q)) := by
  have h := congrArg (fun r : TernaryPolynomial => binaryBoundary (pderiv 0 (pderiv 1 r))) hl
  rw [binaryPeriodLift_mixed_derivative, binaryBoundary_binaryLiftEval',
    binaryBoundary_mixed_coordinate_sum_mul] at h
  exact h.symm

private theorem rotate_injective {r : BP} (h : bind₁ (![-X 1, X 0] : Fin 2 → BP) r = 0) :
    r = 0 := by
  have h' := congrArg (fun p => bind₁ (![X 1, -X 0] : Fin 2 → BP) p) h
  simp only [bind₁_bind₁, map_zero] at h'
  have hv : (fun i => bind₁ (![X 1, -X 0] : Fin 2 → BP) (![-X 1, X 0] i)) = X := by
    funext i
    fin_cases i <;> simp
  rwa [hv, bind₁_X_left, AlgHom.id_apply] at h'

private theorem two_mul_eq_zero {p : BP} (h : p = -p) : p = 0 := by
  have h2 : (2 : BP) * p = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- A symmetric binary period vanishes on the axis `X = 0`. -/
theorem axis_first {q : BP} (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ (![0, X 1] : Fin 2 → BP) q = 0 := by
  have h := congrArg (bind₁ (![0, X 1] : Fin 2 → BP)) hq.odd_first
  rw [bind₁_bind₁, map_neg] at h
  have hv : (fun i => bind₁ (![0, X 1] : Fin 2 → BP) (![-X 0, X 1] i)) = ![0, X 1] := by
    funext i
    fin_cases i <;> simp
  rw [hv] at h
  exact two_mul_eq_zero h

private theorem pderiv_one_axis {q : BP} (hq : SymmetricBinaryPeriodRelations q) :
    bind₁ (![0, X 1] : Fin 2 → BP) (pderiv 1 q) = 0 := by
  have h := congrArg (pderiv (1 : Fin 2)) (axis_first hq)
  simpa [bind_chain_rule] using h

/-- A symmetric binary period with vanishing mixed derivative is zero. -/
theorem eq_zero_of_mixed {q : BP} (hq : SymmetricBinaryPeriodRelations q)
    (h : pderiv 0 (pderiv 1 q) = 0) : q = 0 := by
  have hp : pderiv 1 q = 0 := by
    rw [← binaryIntegral_pderiv_of_axis (pderiv 1 q) (pderiv_one_axis hq), h, map_zero]
  have h0 : pderiv 0 q = 0 := by
    have hs := congrArg (pderiv (0 : Fin 2)) hq.swap
    rw [bind_chain_rule] at hs
    simp only [hp, map_zero, zero_mul, add_zero] at hs
    simpa using hs.symm
  rw [← binaryIntegral_pderiv_of_axis q (axis_first hq), h0, map_zero]

private theorem W_ne_zero : W ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ => (1 : ℚ))) h
  norm_num at this

private theorem binaryPeriodLift_zero : binaryPeriodLift (0 : BP) = 0 := by
  simp [binaryPeriodLift, binaryLiftEval]

/-- **Directness of the tower decomposition.** If `∑_{i<K} w^{2i} l_i = 0` for symmetric binary
periods `q_i` with lifts `Φ(q_i) = w l_i`, then every `q_i` and every `l_i` is zero. -/
theorem tower_eq_zero : ∀ (K : ℕ) (q : ℕ → BP) (l : ℕ → TernaryPolynomial),
    (∀ i < K, SymmetricBinaryPeriodRelations (q i) ∧ binaryPeriodLift (q i) = W * l i) →
    ∑ i ∈ Finset.range K, W ^ (2 * i) * l i = 0 → ∀ i < K, q i = 0 ∧ l i = 0
  | 0, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | K + 1, q, l, hq, hsum, i, hi => by
    have hsplit : ∑ i ∈ Finset.range (K + 1), W ^ (2 * i) * l i =
        l 0 + W ^ 2 * ∑ i ∈ Finset.range K, W ^ (2 * i) * l (i + 1) := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, one_mul, Nat.mul_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, ← pow_add]
      ring_nf
    rw [hsplit] at hsum
    obtain ⟨hq0, hl0⟩ := hq 0 (Nat.succ_pos K)
    have hdata := congrArg firstPlaneData hsum
    rw [firstPlaneData_add, firstPlaneData_W_sq_mul, add_zero, firstPlaneData_lift hl0] at hdata
    rw [firstPlaneData_zero] at hdata
    have hq0z : q 0 = 0 := eq_zero_of_mixed hq0 (rotate_injective hdata)
    have hl0z : l 0 = 0 := by
      rw [hq0z, binaryPeriodLift_zero] at hl0
      exact (mul_eq_zero.mp hl0.symm).resolve_left W_ne_zero
    rw [hl0z, zero_add] at hsum
    have hrest : ∑ i ∈ Finset.range K, W ^ (2 * i) * l (i + 1) = 0 :=
      (mul_eq_zero.mp hsum).resolve_left (pow_ne_zero 2 W_ne_zero)
    rcases i with _ | j
    · exact ⟨hq0z, hl0z⟩
    · exact tower_eq_zero K (fun i => q (i + 1)) (fun i => l (i + 1))
        (fun i hi' => hq (i + 1) (by omega)) hrest j (by omega)

private theorem relations_sub {q q' : BP} (hq : SymmetricBinaryPeriodRelations q)
    (hq' : SymmetricBinaryPeriodRelations q') : SymmetricBinaryPeriodRelations (q - q') where
  swap := by rw [map_sub, hq.swap, hq'.swap]
  odd_first := by rw [map_sub, hq.odd_first, hq'.odd_first]; ring
  odd_second := by rw [map_sub, hq.odd_second, hq'.odd_second]; ring
  period := by
    have h := hq.period
    have h' := hq'.period
    simp only [map_sub]
    linear_combination h - h'

private theorem binaryPeriodLift_sub (q q' : BP) :
    binaryPeriodLift (q - q') = binaryPeriodLift q - binaryPeriodLift q' := by
  simp only [binaryPeriodLift, binaryLiftEval, map_sub]
  ring

/-- Extension by zero of a finite family. -/
def extendZero {α : Type*} [Zero α] {k : ℕ} (f : Fin k → α) (i : ℕ) : α :=
  if h : i < k then f ⟨i, h⟩ else 0

private theorem fin_sum_eq_range {k K : ℕ} (hk : k ≤ K) (l : Fin k → TernaryPolynomial) :
    ∑ i : Fin k, W ^ (2 * (i : ℕ)) * l i =
      ∑ i ∈ Finset.range K, W ^ (2 * i) * extendZero l i := by
  have h1 : ∑ i : Fin k, W ^ (2 * (i : ℕ)) * l i =
      ∑ i : Fin k, W ^ (2 * (i : ℕ)) * extendZero l i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [extendZero, i.isLt]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => W ^ (2 * i) * extendZero l i)]
  refine Finset.sum_subset (Finset.range_mono hk) fun i hiK hik => ?_
  simp only [Finset.mem_range, not_lt] at hik
  simp [extendZero, Nat.not_lt.mpr hik]

/-- **Uniqueness in Lemma 2.3 / Corollary 2.4 (odd degree).** Two towers
`∑_{i<k} w^{2i} L(q_i) = ∑_{i<k'} w^{2i} L(q'_i)` of symmetric binary periods with polynomial lifts
agree term by term (after extension by zero): `q_i = q'_i` and `L(q_i) = L(q'_i)` for every `i`. -/
theorem symmetric_period_tower_unique {k k' : ℕ} (q : Fin k → BP) (l : Fin k → TernaryPolynomial)
    (q' : Fin k' → BP) (l' : Fin k' → TernaryPolynomial)
    (hq : ∀ i, SymmetricBinaryPeriodRelations (q i) ∧ binaryPeriodLift (q i) = W * l i)
    (hq' : ∀ i, SymmetricBinaryPeriodRelations (q' i) ∧ binaryPeriodLift (q' i) = W * l' i)
    (heq : ∑ i : Fin k, W ^ (2 * (i : ℕ)) * l i = ∑ i : Fin k', W ^ (2 * (i : ℕ)) * l' i) :
    ∀ j : ℕ, extendZero q j = extendZero q' j ∧ extendZero l j = extendZero l' j := by
  set K := max k k'
  have hext : ∀ {m : ℕ} (p : Fin m → BP) (r : Fin m → TernaryPolynomial),
      (∀ i, SymmetricBinaryPeriodRelations (p i) ∧ binaryPeriodLift (p i) = W * r i) →
      ∀ j, SymmetricBinaryPeriodRelations (extendZero p j) ∧
        binaryPeriodLift (extendZero p j) = W * extendZero r j := by
    intro m p r hp j
    by_cases hj : j < m
    · simpa [extendZero, hj] using hp ⟨j, hj⟩
    · simp only [extendZero, hj, dite_false, binaryPeriodLift_zero, mul_zero, and_true]
      exact ⟨by simp, by simp, by simp, by simp⟩
  have hzero := tower_eq_zero K (fun j => extendZero q j - extendZero q' j)
    (fun j => extendZero l j - extendZero l' j)
    (fun j _ => ⟨relations_sub (hext q l hq j).1 (hext q' l' hq' j).1, by
      rw [binaryPeriodLift_sub, (hext q l hq j).2, (hext q' l' hq' j).2]; ring⟩)
    (by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← fin_sum_eq_range (le_max_left k k') l, ← fin_sum_eq_range (le_max_right k k') l',
        heq, sub_self])
  intro j
  by_cases hj : j < K
  · obtain ⟨h1, h2⟩ := hzero j hj
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  · have hjk : ¬ j < k := fun h => hj (lt_of_lt_of_le h (le_max_left k k'))
    have hjk' : ¬ j < k' := fun h => hj (lt_of_lt_of_le h (le_max_right k k'))
    simp [extendZero, hjk, hjk']

/-- **Uniqueness in Corollary 2.4 (even degree).** Two towers
`∑_{i<k} w^{2i} Φ(q_i) = ∑_{i<k'} w^{2i} Φ(q'_i)` of symmetric binary periods agree term by term
(after extension by zero). -/
theorem symmetric_even_period_tower_unique {k k' : ℕ} (q : Fin k → BP) (q' : Fin k' → BP)
    (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (hq' : ∀ i, SymmetricBinaryPeriodRelations (q' i))
    (heq : ∑ i : Fin k, W ^ (2 * (i : ℕ)) * binaryPeriodLift (q i) =
      ∑ i : Fin k', W ^ (2 * (i : ℕ)) * binaryPeriodLift (q' i)) :
    ∀ j : ℕ, extendZero q j = extendZero q' j := by
  choose l hl using fun i => coordinate_sum_dvd_symmetricBinaryLift (hq i)
  choose l' hl' using fun i => coordinate_sum_dvd_symmetricBinaryLift (hq' i)
  have hsum : W * ∑ i : Fin k, W ^ (2 * (i : ℕ)) * l i =
      W * ∑ i : Fin k', W ^ (2 * (i : ℕ)) * l' i := by
    simp only [Finset.mul_sum]
    have e1 : ∀ i : Fin k, W * (W ^ (2 * (i : ℕ)) * l i) =
        W ^ (2 * (i : ℕ)) * binaryPeriodLift (q i) := fun i => by rw [hl i]; ring
    have e2 : ∀ i : Fin k', W * (W ^ (2 * (i : ℕ)) * l' i) =
        W ^ (2 * (i : ℕ)) * binaryPeriodLift (q' i) := fun i => by rw [hl' i]; ring
    simp only [e1, e2]
    exact heq
  have hcancel := mul_left_cancel₀ W_ne_zero hsum
  exact fun j => (symmetric_period_tower_unique q l q' l' (fun i => ⟨hq i, hl i⟩)
    (fun i => ⟨hq' i, hl' i⟩) hcancel j).1

/-- **Lemma 2.3 (`lem:period-extraction`), the common-kernel equivalence.** For odd `m` and a
symmetric (`C v = v`, `S v = v`) homogeneous `v ∈ V_m`: `J_v = 0` iff `v = ∑_{i<k} w^{2i} L(q_i)` for
symmetric binary periods `q_i ∈ 𝓑_{m+1-2i}` (`SymmetricBinaryPeriodRelations`, homogeneous of degree
`m + 1 - 2i`) with polynomial lifts `Φ(q_i) = w L(q_i)`. The expression is unique by
`symmetric_period_tower_unique`; every `q ∈ 𝓑_d` has a polynomial lift by
`TernaryPoly.coordinate_sum_dvd_symmetricBinaryLift`. Here `J` is `TernaryPoly.symmetricTodd`. -/
theorem lemma_2_3 {v : TernaryPolynomial} {m : ℕ} (hv : v.IsHomogeneous m) (hm : Odd m)
    (hc : TernaryPoly.C v = v) (hs : TernaryPoly.S v = v) :
    symmetricTodd v = 0 ↔
      ∃ k : ℕ, ∃ q : Fin k → BP, ∃ l : Fin k → TernaryPolynomial,
        (∀ i, SymmetricBinaryPeriodRelations (q i) ∧ (q i).IsHomogeneous (m + 1 - 2 * (i : ℕ)) ∧
          binaryPeriodLift (q i) = W * l i) ∧
        v = ∑ i : Fin k, W ^ (2 * (i : ℕ)) * l i := by
  constructor
  · exact symmetric_odd_period_tower hv hm hc hs
  · rintro ⟨k, q, l, hq, rfl⟩
    exact symmetric_period_tower_Todd_zero q l (fun i => (hq i).1) (fun i => (hq i).2.2)

end TernaryPeriodPolynomials.Argument.Statements.PeriodTowers
