module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.ReparamInjective
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.ReduceTwoBasic
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.OperatorAdditivity
public import TernaryPeriodPolynomials.AlternatingSolution.CoefficientPolynomials
public import TernaryPeriodPolynomials.AlternatingSolution.TriangularTable

@[expose] public section



/-! `expandOdd` has trivial kernel: `expandOdd s = 0 → s = 0` for `s : Fin 8 → Poly2`. Used in
the proof of Theorem 5.2 (`mf:thm:main`), step `mf:lem:cancellation`, to turn
`expandOdd (r + uOperator r) = 0` into `r + uOperator r = 0`.

The argument: `evalR0` factors as `invariantEval ∘ reparam` (`ReparamInjective.lean`), so each
term `evalR0 (s j) * oddGenerator j` of `expandOdd s` equals
`invariantEval (reparam (s j) * X 2 ^ kappa j) * generator j`. Comparing the resulting
`∑ j, invariantEval (w j) * generator j = 0` with the trivial witness for `0` under `charTwo_normKernel_free`'s
uniqueness clause forces `w j = reparam (s j) * X 2 ^ kappa j = 0` for every `j`; since `Poly2` is
a domain and `X 2 ^ kappa j ≠ 0`, `reparam (s j) = 0`, and `reparam_injective` gives `s j = 0`. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument

/-- `evalR0` factors through `reparam` and `invariantEval`. -/
theorem evalR0_eq_invariantEval_reparam (h : Poly2) :
    invariantEval (reparam h) = evalR0 h := by
  have hfun : (fun i : Fin 3 => bind₁ TernaryPoly.CharTwoNorm.invariant
      ((![X 0, X 1, X 2 ^ 2] : Fin 3 → Poly2) i)) = (![d4, d6, d7 ^ 2] : Fin 3 → Poly2) := by
    funext i
    fin_cases i <;>
      simp [TernaryPoly.CharTwoNorm.invariant, bind₁_X_right, map_pow]
  show bind₁ TernaryPoly.CharTwoNorm.invariant (bind₁ ![X 0, X 1, X 2 ^ 2] h)
      = bind₁ ![d4, d6, d7 ^ 2] h
  rw [bind₁_bind₁, hfun]

private theorem invariantEval_X2 : invariantEval (X 2 : Poly2) = d7 := by
  show bind₁ TernaryPoly.CharTwoNorm.invariant (X 2) = d7
  rw [bind₁_X_right]
  simp [TernaryPoly.CharTwoNorm.invariant]

/-- The per-generator identity turning a term of `expandOdd` into an `invariantEval`-expansion
term, via `reparam`. -/
theorem evalR0_mul_oddGenerator (p : Poly2) (j : Fin 8) :
    evalR0 p * oddGenerator j = invariantEval (reparam p * X 2 ^ kappa j) * generator j := by
  rw [map_mul, map_pow, evalR0_eq_invariantEval_reparam, invariantEval_X2]
  show evalR0 p * (generator j * d7 ^ kappa j) = evalR0 p * d7 ^ kappa j * generator j
  ring

/-- `expandOdd` has trivial kernel. -/
theorem expandOdd_eq_zero {s : Fin 8 → Poly2} (hs : expandOdd s = 0) : s = 0 := by
  have hw : (0 : Poly2) =
      ∑ j, invariantEval (reparam (s j) * X 2 ^ kappa j) * generator j := by
    have hsum : ∑ j, invariantEval (reparam (s j) * X 2 ^ kappa j) * generator j
        = expandOdd s := by
      show ∑ j, invariantEval (reparam (s j) * X 2 ^ kappa j) * generator j
          = ∑ j, evalR0 (s j) * oddGenerator j
      exact Finset.sum_congr rfl (fun j _ => (evalR0_mul_oddGenerator (s j) j).symm)
    rw [hsum, hs]
  have hsymm0 : (0 : Poly2).IsSymmetric := by
    intro e
    exact map_zero _
  obtain ⟨r0, _, huniq⟩ := (charTwo_normKernel_free.2 0 hsymm0).mp TernaryPoly.CharTwoNorm.norm_zero
  have hw0 : (fun j => reparam (s j) * X 2 ^ kappa j) = r0 := huniq _ hw
  have h00 : (0 : Fin 8 → Poly2) = r0 := huniq 0 (by simp)
  have hweq0 : (fun j => reparam (s j) * X 2 ^ kappa j) = (0 : Fin 8 → Poly2) :=
    hw0.trans h00.symm
  funext j
  have hwj : reparam (s j) * X 2 ^ kappa j = 0 := congrFun hweq0 j
  have hx2j : (X 2 : Poly2) ^ kappa j ≠ 0 := pow_ne_zero _ (X_ne_zero 2)
  have hrp : reparam (s j) = 0 := by
    rcases mul_eq_zero.mp hwj with h1 | h2
    · exact h1
    · exact absurd h2 hx2j
  exact reparam_injective (hrp.trans (map_zero reparam).symm)

/-- If `expandOdd r + expandOdd (uOperator r) = 0`, then `r = 0`. Combines the kernel-triviality
of `expandOdd` above with `modFour_beta_triangular`'s period-three identity for `uOperator` and the char-two
self-negation of `Poly2`. -/
theorem r_eq_zero_of_expandOdd_sum_eq_zero (r : Fin 8 → Poly2)
    (hr : expandOdd r + expandOdd (uOperator r) = 0) : r = 0 := by
  have h1 : expandOdd (r + uOperator r) = 0 := by rw [expandOdd_add]; exact hr
  have h2 : r + uOperator r = 0 := expandOdd_eq_zero h1
  have h3 : uOperator r = r := by
    funext j
    have hj : r j + uOperator r j = 0 := congrFun h2 j
    have hj' : uOperator r j + r j = 0 := by rw [add_comm]; exact hj
    exact (eq_neg_of_add_eq_zero_left hj').trans (neg_eq_self_two (r j))
  have h4 : uOperator (uOperator (uOperator r)) = r := by rw [h3, h3, h3]
  have h5 : uOperator (uOperator (uOperator r)) = 0 := modFour_beta_triangular.2 r
  rw [h5] at h4
  exact h4.symm

end TernaryPeriodPolynomials.Argument
