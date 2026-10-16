module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GenAbsHomogeneous
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.DicksonWeights
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.WeightedComponent
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.AevalComponent

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly a b c d4 d6 d7 invariantEval standardMonomial)

/-- `a` is `![4,6,7]`-weighted-homogeneous of degree `4` (the *coefficient-side* role of `a`,
dual to `d4` via `invariantEval a = d4`; distinct from `isWeightedHomogeneous_a`, which is the
*ambient-side* `stdWeight`-degree-`1` fact about the same term `a`). -/
theorem isWeightedHomogeneous_a_467 : IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) a 4 := by
  simpa [a] using isWeightedHomogeneous_X (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ) (0 : Fin 3)

theorem isWeightedHomogeneous_b_467 : IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) b 6 := by
  simpa [b] using isWeightedHomogeneous_X (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ) (1 : Fin 3)

theorem isWeightedHomogeneous_c_467 : IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) c 7 := by
  simpa [c] using isWeightedHomogeneous_X (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ) (2 : Fin 3)

/-- `d4, d6, d7` are `stdWeight`-homogeneous at the matching `![4,6,7]` degree, repackaged as a
`∀ j : Fin 3` family (the shape `weightedHomogeneousComponent_aeval`/`isWeightedHomogeneous_aeval`
need). Lifted out of `PsiMap.lean`'s `isWeightedHomogeneous_invariantEval` proof so it is directly
reusable here too. -/
theorem hhom_467 : ∀ j : Fin 3,
    IsWeightedHomogeneous stdWeight ((![d4, d6, d7] : Fin 3 → Poly) j)
      ((![4, 6, 7] : Fin 3 → ℕ) j) := by
  intro j
  fin_cases j
  · simpa using isWeightedHomogeneous_d4
  · simpa using isWeightedHomogeneous_d6
  · simpa using isWeightedHomogeneous_d7

/-- **Lemma A, degree-`N` single-row extraction.** The degree-`N` `stdWeight`-component of
`invariantEval q * genAbs i` either vanishes (`genAbsDeg i > N`) or equals `invariantEval` of the
truncated `![4,6,7]`-component of `q`, times `genAbs i` back (`genAbsDeg i ≤ N`). -/
theorem weightedHomogeneousComponent_invariantEval_mul_genAbs (i : Fin 8) (q : Poly) (N : ℕ) :
    weightedHomogeneousComponent stdWeight N (invariantEval q * genAbs i) =
      if genAbsDeg i ≤ N then
        invariantEval (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (N - genAbsDeg i) q) *
          genAbs i
      else 0 := by
  split_ifs with h
  · have e1 := weightedHomogeneousComponent_mul_of_homog (isWeightedHomogeneous_genAbs i)
      (invariantEval q) (N - genAbsDeg i)
    rw [Nat.sub_add_cancel h] at e1
    rw [e1, show invariantEval = aeval (R := ZMod 2) ![d4, d6, d7] from rfl,
      weightedHomogeneousComponent_aeval hhom_467]
  · exact weightedHomogeneousComponent_mul_eq_zero_of_lt (isWeightedHomogeneous_genAbs i) _
      (by omega)

/-- **Lemma A, degree-`N` global extraction.** Taking the degree-`N` `stdWeight`-component of the
global hypothesis `∑ i, invariantEval (p i) * genAbs i = 0` termwise. -/
theorem weightedHomogeneousComponent_sum_invariantEval_mul_genAbs
    (p : Fin 8 → Poly) (N : ℕ)
    (hsum : ∑ i : Fin 8, invariantEval (p i) * genAbs i = 0) :
    ∑ i : Fin 8, (if genAbsDeg i ≤ N then
        invariantEval
          (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (N - genAbsDeg i) (p i)) *
          genAbs i
      else 0) = 0 := by
  have hc := congrArg (weightedHomogeneousComponent stdWeight N) hsum
  rw [map_sum, map_zero] at hc
  have hterm : ∑ i : Fin 8, weightedHomogeneousComponent stdWeight N (invariantEval (p i) * genAbs i) =
      ∑ i : Fin 8, (if genAbsDeg i ≤ N then
          invariantEval
            (weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (N - genAbsDeg i) (p i)) *
            genAbs i
        else 0) :=
    Finset.sum_congr rfl (fun i _ => weightedHomogeneousComponent_invariantEval_mul_genAbs i (p i) N)
  rw [← hterm]
  exact hc

end TernaryPeriodPolynomials.Argument.CharTwoKernel
