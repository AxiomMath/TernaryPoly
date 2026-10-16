module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.StandardHomogeneous
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.AevalComponent
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.WeightedComponent
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.DicksonWeights

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly standardMonomial invariantEval exists_standard_expansion
  d4 d6 d7)

/-- **Ψ_d surjectivity's raw ingredient.** Every `stdWeight`-homogeneous
polynomial of degree `n` has an expansion in the 28 `standardMonomial`s whose coefficients are
`![4,6,7]`-homogeneous of the matching (truncated) degree. Combines the ungraded expansion
`exists_standard_expansion` with a degree-`n` projection: applying `weightedHomogeneousComponent
stdWeight n` to both sides of the ungraded expansion, each term either vanishes (if `stdDeg i > n`,
via `weightedHomogeneousComponent_mul_eq_zero_of_lt`) or contributes its own truncated-degree
component (if `stdDeg i ≤ n`, via `weightedHomogeneousComponent_mul_of_homog` plus the
`aeval`-commutation lemma `weightedHomogeneousComponent_aeval`, using that `invariantEval` unfolds
definitionally to `aeval ![d4,d6,d7]`). In particular, instantiating at each `genAbs i` (each of
which is itself `stdWeight`-homogeneous) gives Item 2's eight expansions for free, with no need for
hand-derived normal forms. -/
theorem homogeneous_expand {f : Poly} {n : ℕ} (hf : IsWeightedHomogeneous stdWeight f n) :
    ∃ c : Fin 28 → Poly,
      (∀ i, IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (c i) (n - stdDeg i)) ∧
        f = ∑ i, invariantEval (c i) * standardMonomial i := by
  classical
  obtain ⟨coeff, hcoeff⟩ := exists_standard_expansion f
  have hhom : ∀ j : Fin 3,
      IsWeightedHomogeneous stdWeight ((![d4, d6, d7] : Fin 3 → Poly) j)
        ((![4, 6, 7] : Fin 3 → ℕ) j) := by
    intro j
    fin_cases j
    · simpa using isWeightedHomogeneous_d4
    · simpa using isWeightedHomogeneous_d6
    · simpa using isWeightedHomogeneous_d7
  refine ⟨fun i => if stdDeg i ≤ n then
      weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (n - stdDeg i) (coeff i) else 0,
    fun i => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
    · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.zero_mem _)
  · calc f = weightedHomogeneousComponent stdWeight n f := hf.weightedHomogeneousComponent_same.symm
      _ = weightedHomogeneousComponent stdWeight n
            (∑ i, invariantEval (coeff i) * standardMonomial i) := by rw [hcoeff]
      _ = ∑ i, weightedHomogeneousComponent stdWeight n
            (invariantEval (coeff i) * standardMonomial i) := by rw [map_sum]
      _ = ∑ i, invariantEval (if stdDeg i ≤ n then
            weightedHomogeneousComponent (![4, 6, 7] : Fin 3 → ℕ) (n - stdDeg i) (coeff i)
          else 0) * standardMonomial i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          split_ifs with h
          · conv_lhs => rw [show n = (n - stdDeg i) + stdDeg i from by omega]
            rw [weightedHomogeneousComponent_mul_of_homog (isWeightedHomogeneous_standardMonomial i),
              show invariantEval = aeval (R := ZMod 2) ![d4, d6, d7] from rfl,
              weightedHomogeneousComponent_aeval hhom]
          · rw [weightedHomogeneousComponent_mul_eq_zero_of_lt
              (isWeightedHomogeneous_standardMonomial i) _ (by omega), map_zero, zero_mul]

end TernaryPeriodPolynomials.Argument.CharTwoKernel
