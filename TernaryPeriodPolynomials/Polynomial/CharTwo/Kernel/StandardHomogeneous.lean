module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.DicksonWeights
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.HilbertSeries
public import TernaryPeriodPolynomials.Polynomial.DicksonQuotient

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial
open TernaryPoly.DicksonQuotient (standardMonomial)






/-- **Item 2, prerequisite.** Every `standardMonomial i` is `stdWeight`-weighted-homogeneous of
degree `stdDeg i`. Proved by `fin_cases` on `i`, unfolding both arrays and closing each of the 28
resulting goals by combining `isWeightedHomogeneous_a/b/c` (from `DicksonWeights.lean`) via `.mul`
and `.pow`. -/
theorem isWeightedHomogeneous_standardMonomial (i : Fin 28) :
    IsWeightedHomogeneous stdWeight (standardMonomial i) (stdDeg i) := by
  fin_cases i <;> simp only [standardMonomial, stdDeg]
  · simpa using isWeightedHomogeneous_one (ZMod 2) stdWeight
  · simpa using isWeightedHomogeneous_a
  · simpa using isWeightedHomogeneous_b
  · simpa using isWeightedHomogeneous_a.pow 2
  · simpa using isWeightedHomogeneous_c
  · simpa using isWeightedHomogeneous_a.mul isWeightedHomogeneous_b
  · simpa using isWeightedHomogeneous_a.pow 3
  · simpa using isWeightedHomogeneous_b.pow 2
  · simpa using isWeightedHomogeneous_a.mul isWeightedHomogeneous_c
  · simpa using (isWeightedHomogeneous_a.pow 2).mul isWeightedHomogeneous_b
  · simpa using isWeightedHomogeneous_b.mul isWeightedHomogeneous_c
  · simpa using isWeightedHomogeneous_a.mul (isWeightedHomogeneous_b.pow 2)
  · simpa using (isWeightedHomogeneous_a.pow 2).mul isWeightedHomogeneous_c
  · simpa using (isWeightedHomogeneous_a.pow 3).mul isWeightedHomogeneous_b
  · simpa using isWeightedHomogeneous_c.pow 2
  · simpa using isWeightedHomogeneous_b.pow 3
  · simpa using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_b).mul isWeightedHomogeneous_c
  · simpa using (isWeightedHomogeneous_a.pow 2).mul (isWeightedHomogeneous_b.pow 2)
  · simpa using (isWeightedHomogeneous_b.pow 2).mul isWeightedHomogeneous_c
  · simpa using isWeightedHomogeneous_a.mul (isWeightedHomogeneous_c.pow 2)
  · simpa using isWeightedHomogeneous_a.mul (isWeightedHomogeneous_b.pow 3)
  · simpa using isWeightedHomogeneous_b.mul (isWeightedHomogeneous_c.pow 2)
  · simpa using isWeightedHomogeneous_b.pow 4
  · simpa using (isWeightedHomogeneous_a.mul (isWeightedHomogeneous_b.pow 2)).mul
      isWeightedHomogeneous_c
  · simpa using isWeightedHomogeneous_c.pow 3
  · simpa using (isWeightedHomogeneous_b.pow 3).mul isWeightedHomogeneous_c
  · simpa using isWeightedHomogeneous_b.pow 5
  · simpa using isWeightedHomogeneous_b.mul (isWeightedHomogeneous_c.pow 3)

end TernaryPeriodPolynomials.Argument.CharTwoKernel
