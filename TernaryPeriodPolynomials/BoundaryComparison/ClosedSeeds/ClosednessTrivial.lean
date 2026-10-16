module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section


/-! Clause (i) of Lemma C.3 (`ar:lem:seed`), "trivial" cases: the alternating-sum-of-partials
expression `Alt3 n h m p i j k` (clause (i)'s left-hand side) vanishes identically whenever
`i, j, k : Fin 5` are not pairwise distinct elements of `{0, 1, 2, 3}`. There are `125 - 24 = 101`
such triples, out of all `5^3 = 125`; they are disposed of here by two generic facts rather than
by case-by-case computation:

* `Alt3` is alternating: transposing any two of its three index arguments negates it
  (`Alt3_swap_ij`, `Alt3_swap_jk`, and the derived `Alt3_swap_ik`, since the first two
  transpositions generate all of `S₃`). An alternating quantity with two equal arguments is its
  own negation, hence `0` in a field of characteristic `≠ 2` (`Alt3_eq_ij`, `Alt3_eq_jk`,
  `Alt3_eq_ik`): this disposes of the `5² · 3 - 5² · (\text{double-counted}) ` triples with a
  repeated index (not an exact partition, but the disjunction suffices).
* `seedBeta` and `seedDTau` literally vanish in direction `4` (the seed is independent of the
  normal height and has no `dt` component), so `seedForm` — hence `Alt3` — vanishes whenever `4`
  occurs in any of the three slots (`Alt3_dim4_right` directly, `Alt3_dim4_mid`/`Alt3_dim4_left`
  by propagating `Alt3_dim4_right` through the alternating symmetry).

Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. The remaining `24` triples (pairwise
distinct indices from `{0, 1, 2, 3}`) are the genuine content of clause (i) and are handled
elsewhere. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `seedForm` is antisymmetric in its last two indices. -/
theorem seedForm_antisymm (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    seedForm n h p j i = - seedForm n h p i j := by
  unfold seedForm
  rw [show (seedBeta p j * seedDTau i - seedBeta p i * seedDTau j) =
      -(seedBeta p i * seedDTau j - seedBeta p j * seedDTau i) by ring, mul_neg, map_neg, neg_mul]

/-- `seedForm` vanishes whenever its second index is `4` (`seedBeta`/`seedDTau` are literally
zero in direction `4`). -/
theorem seedForm_dim4_right (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (a : Fin 5) :
    seedForm n h p a 4 = 0 := by simp [seedForm, seedDTau, seedBeta]

/-- `coordPartial` of a function of `q` reading only `seedForm n h q a b` vanishes along
coordinate `4`, since `seedForm` itself does not depend on coordinate `4`. -/
theorem coordPartial_dim4_zero (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (a b : Fin 5) :
    coordPartial (fun q => (seedForm n h q a b).coeff m) 4 p = 0 := by
  unfold coordPartial
  have heq : (fun s : ℝ => (seedForm n h (Function.update p 4 s) a b).coeff m) =
      fun _ : ℝ => (seedForm n h p a b).coeff m := by
    funext s
    simp [seedForm, seedTau, seedBeta, seedLinear]
  rw [heq]
  exact deriv_const _ _

/-- `coordPartial` commutes with negation. -/
theorem coordPartial_neg (f : (Fin 5 → ℝ) → ℂ) (k : Fin 5) (p : Fin 5 → ℝ) :
    coordPartial (fun q => - f q) k p = - coordPartial f k p := by
  unfold coordPartial
  exact deriv.neg

/-- `coordPartial` of a constant function vanishes. -/
theorem coordPartial_const (c : ℂ) (k : Fin 5) (p : Fin 5 → ℝ) :
    coordPartial (fun _ => c) k p = 0 := by
  unfold coordPartial; exact deriv_const _ _

/-- The `m`-coefficient of `seedForm`, as a function of `q`, is pointwise antisymmetric in its
last two indices. -/
theorem coeff_seedForm_neg (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (i j : Fin 5) :
    (fun q => (seedForm n h q j i).coeff m) = fun q => - (seedForm n h q i j).coeff m := by
  funext q
  rw [seedForm_antisymm,
    show (-(seedForm n h q i j)) = (-1 : ℂ) • seedForm n h q i j from (neg_one_smul ℂ _).symm,
    coeff_smul, smul_eq_mul]
  ring

/-- `Alt3 n h m p i j k` is the alternating-sum-of-coordinate-partials expression that clause (i)
of Lemma C.3 (`ar:lem:seed`) asserts vanishes for every `i j k : Fin 5`. -/
noncomputable def Alt3 (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i j k : Fin 5) : ℂ :=
  coordPartial (fun q => (seedForm n h q j k).coeff m) i p -
    coordPartial (fun q => (seedForm n h q i k).coeff m) j p +
    coordPartial (fun q => (seedForm n h q i j).coeff m) k p

/-- `Alt3` is antisymmetric under swapping its first two index arguments. -/
theorem Alt3_swap_ij (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i j k : Fin 5) :
    Alt3 n h m p j i k = - Alt3 n h m p i j k := by
  unfold Alt3
  rw [coeff_seedForm_neg n h m j i, coordPartial_neg]
  ring

/-- `Alt3` is antisymmetric under swapping its last two index arguments. -/
theorem Alt3_swap_jk (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i j k : Fin 5) :
    Alt3 n h m p i k j = - Alt3 n h m p i j k := by
  unfold Alt3
  rw [coeff_seedForm_neg n h m k j, coordPartial_neg]
  ring

/-- `Alt3` is antisymmetric under swapping its first and third index arguments: a consequence of
the two adjacent transpositions above, since they generate all of `S₃`. -/
theorem Alt3_swap_ik (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i j k : Fin 5) :
    Alt3 n h m p k j i = - Alt3 n h m p i j k := by
  have h1 := Alt3_swap_ij n h m p i j k
  have h2 := Alt3_swap_jk n h m p j i k
  have h3 := Alt3_swap_ij n h m p j k i
  calc Alt3 n h m p k j i = - Alt3 n h m p j k i := h3
    _ = - (- Alt3 n h m p j i k) := by rw [h2]
    _ = Alt3 n h m p j i k := by ring
    _ = - Alt3 n h m p i j k := h1

/-- A complex number equal to its own negation is zero (char. `0`). -/
theorem eq_zero_of_eq_neg_self {a : ℂ} (h : a = -a) : a = 0 := by
  linear_combination (1 / 2 : ℂ) * h

/-- `Alt3` vanishes whenever its first two index arguments coincide. -/
theorem Alt3_eq_ij (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i k : Fin 5) :
    Alt3 n h m p i i k = 0 :=
  eq_zero_of_eq_neg_self (Alt3_swap_ij n h m p i i k)

/-- `Alt3` vanishes whenever its last two index arguments coincide. -/
theorem Alt3_eq_jk (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    Alt3 n h m p i j j = 0 :=
  eq_zero_of_eq_neg_self (Alt3_swap_jk n h m p i j j)

/-- `Alt3` vanishes whenever its first and third index arguments coincide. -/
theorem Alt3_eq_ik (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    Alt3 n h m p i j i = 0 :=
  eq_zero_of_eq_neg_self (Alt3_swap_ik n h m p i j i)

/-- `Alt3` vanishes whenever its third index argument is `4`. -/
theorem Alt3_dim4_right (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    Alt3 n h m p i j 4 = 0 := by
  unfold Alt3
  have e1 : (fun q => (seedForm n h q j 4).coeff m) = fun _ : Fin 5 → ℝ => (0 : ℂ) := by
    funext q; rw [seedForm_dim4_right, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have e2 : (fun q => (seedForm n h q i 4).coeff m) = fun _ : Fin 5 → ℝ => (0 : ℂ) := by
    funext q; rw [seedForm_dim4_right, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  rw [e1, e2, coordPartial_const, coordPartial_const, coordPartial_dim4_zero n h m p i j]
  ring

/-- `Alt3` vanishes whenever its second index argument is `4`. -/
theorem Alt3_dim4_mid (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (i k : Fin 5) :
    Alt3 n h m p i 4 k = 0 := by
  have hswap := Alt3_swap_jk n h m p i 4 k
  rw [Alt3_dim4_right] at hswap
  linear_combination hswap

/-- `Alt3` vanishes whenever its first index argument is `4`. -/
theorem Alt3_dim4_left (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (j k : Fin 5) :
    Alt3 n h m p 4 j k = 0 := by
  have hswap := Alt3_swap_ik n h m p 4 j k
  rw [Alt3_dim4_right] at hswap
  linear_combination hswap

end TernaryPeriodPolynomials.Argument
