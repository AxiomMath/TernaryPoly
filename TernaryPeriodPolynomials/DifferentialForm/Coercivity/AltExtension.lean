module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeStar

@[expose] public section



/-! Canonical alternating extensions `altTwo`/`altThree`. Substituting `a = altTwo a` (resp.
`b = altThree b`) for an alternating `a`/`b` turns every later occurrence of `a`/`b` applied to
concrete indices into an explicit `if`-reduced value, so the Hodge-star identities in the sibling
files here can be proved by `fin_cases` + `simp` + `module` without ever rewriting with
`IsAlternatingTwo`/`IsAlternatingThree` themselves. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

/-- If `x` is its own negative in the `ℝ`-vector space `Poly`, it is zero. -/
theorem poly_self_neg_eq_zero {x : Poly} (h : x = -x) : x = 0 := by
  have h2 : x + x = 0 := by nth_rewrite 2 [h]; abel
  have h3 : (2 : ℝ) • x = 0 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
    exact h2
  have h4 : (2 : ℝ)⁻¹ • ((2 : ℝ) • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  rw [← h4, h3, smul_zero]

/-- Canonical alternating extension of an arbitrary `c : TwoCoordinates`: zero on the diagonal,
and off the diagonal reads `c` at the increasing order of the pair, flipping sign if the given
order is decreasing. -/
def altTwo (c : TwoCoordinates) : TwoCoordinates :=
  fun i j => if i < j then c i j else if j < i then -c j i else 0

theorem altTwo_eq_of_alternating {a : TwoCoordinates} (ha : IsAlternatingTwo a) :
    a = altTwo a := by
  funext i j
  show a i j = if i < j then a i j else if j < i then -a j i else 0
  rcases lt_trichotomy i j with h | h | h
  · rw [ite_eq_left h]
  · subst h
    rw [ite_eq_right (lt_irrefl i), ite_eq_right (lt_irrefl i)]
    exact poly_self_neg_eq_zero (ha i i)
  · rw [ite_eq_right (lt_asymm h), ite_eq_left h]
    exact ha i j

/-- The "swap last two" transposition for an alternating `ThreeCoordinates`, derived from the
defining swap-first-two and cyclic clauses. -/
theorem alternatingThree_swap12 {a : ThreeCoordinates} (ha : IsAlternatingThree a)
    (i j k : Fin 5) : a i j k = -a i k j :=
  (ha.2 i j k).trans (ha.1 k i j)

/-- The "swap first and last" transposition for an alternating `ThreeCoordinates`. -/
theorem alternatingThree_swap02 {a : ThreeCoordinates} (ha : IsAlternatingThree a)
    (i j k : Fin 5) : a i j k = -a k j i := by
  rw [ha.1 i j k, ha.2 j i k]

theorem alternatingThree_diag12 {a : ThreeCoordinates} (ha : IsAlternatingThree a)
    (i k : Fin 5) : a i i k = 0 :=
  poly_self_neg_eq_zero (ha.1 i i k)

theorem alternatingThree_diag23 {a : ThreeCoordinates} (ha : IsAlternatingThree a)
    (i j : Fin 5) : a i j j = 0 :=
  poly_self_neg_eq_zero (alternatingThree_swap12 ha i j j)

theorem alternatingThree_diag13 {a : ThreeCoordinates} (ha : IsAlternatingThree a)
    (i j : Fin 5) : a i j i = 0 :=
  poly_self_neg_eq_zero (alternatingThree_swap02 ha i j i)

/-- Canonical alternating extension of an arbitrary `c : ThreeCoordinates`: zero on any repeated
index, and on distinct indices reads `c` at the increasing order of the triple, signed by the
parity of the permutation needed to reach that order. -/
def altThree (c : ThreeCoordinates) : ThreeCoordinates :=
  fun i j k =>
    if i < j ∧ j < k then c i j k
    else if i < k ∧ k < j then -c i k j
    else if j < i ∧ i < k then -c j i k
    else if j < k ∧ k < i then c j k i
    else if k < i ∧ i < j then c k i j
    else if k < j ∧ j < i then -c k j i
    else 0

theorem altThree_eq_of_alternating {a : ThreeCoordinates} (ha : IsAlternatingThree a) :
    a = altThree a := by
  funext i j k
  show a i j k = (if i < j ∧ j < k then a i j k
    else if i < k ∧ k < j then -a i k j
    else if j < i ∧ i < k then -a j i k
    else if j < k ∧ k < i then a j k i
    else if k < i ∧ i < j then a k i j
    else if k < j ∧ j < i then -a k j i
    else 0)
  split_ifs with h1 h2 h3 h4 h5 h6
  · rfl
  · exact alternatingThree_swap12 ha i j k
  · exact ha.1 i j k
  · exact (ha.2 i j k).trans (ha.2 k i j)
  · exact ha.2 i j k
  · exact alternatingThree_swap02 ha i j k
  · have hcase : i = j ∨ j = k ∨ i = k := by omega
    rcases hcase with h | h | h
    · rw [h]; exact alternatingThree_diag12 ha j k
    · rw [h]; exact alternatingThree_diag23 ha i k
    · rw [h]; exact alternatingThree_diag13 ha k j

end TernaryPeriodPolynomials.Argument.Coercivity
