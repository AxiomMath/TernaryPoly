module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GeneratorAbstract
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.HomogeneousExpand

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly a b c invariantEval standardMonomial)

/-- `stdWeight`-degree of each of the 8 abstract `basisAbs` elements, read off their literal
formulas (`![1, a, a^2+b, a*b, a^3+c, a*cplusAbs, a^3*(a^2+b), a^6+a^3*c+b^3+c^2]`). -/
def basisDeg : Fin 8 → ℕ := ![0, 1, 2, 3, 3, 4, 5, 6]

/-- `stdWeight`-degree of each of the 8 abstract `genAbs i = a * cplusAbs * basisAbs i`
generators: `4 + basisDeg i` since `a * cplusAbs` has degree `1 + 3 = 4`. -/
def genAbsDeg : Fin 8 → ℕ := ![4, 5, 6, 7, 7, 8, 9, 10]

theorem isWeightedHomogeneous_cplusAbs : IsWeightedHomogeneous stdWeight cplusAbs 3 := by
  simpa [cplusAbs] using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_b).add
    isWeightedHomogeneous_c

/-- **Item 2, prerequisite.** Every `basisAbs i` is `stdWeight`-homogeneous of degree `basisDeg i`.
Proved by `fin_cases` on `i`, combining `isWeightedHomogeneous_a/b/c` and
`isWeightedHomogeneous_cplusAbs` via `.mul`/`.add`/`.pow`. -/
theorem isWeightedHomogeneous_basisAbs (i : Fin 8) :
    IsWeightedHomogeneous stdWeight (basisAbs i) (basisDeg i) := by
  fin_cases i <;> simp only [basisAbs, basisDeg]
  · simpa using isWeightedHomogeneous_one (ZMod 2) stdWeight
  · simpa using isWeightedHomogeneous_a
  · simpa using (isWeightedHomogeneous_a.pow 2).add isWeightedHomogeneous_b
  · simpa using isWeightedHomogeneous_a.mul isWeightedHomogeneous_b
  · simpa using (isWeightedHomogeneous_a.pow 3).add isWeightedHomogeneous_c
  · simpa using isWeightedHomogeneous_a.mul isWeightedHomogeneous_cplusAbs
  · simpa using (isWeightedHomogeneous_a.pow 3).mul
      ((isWeightedHomogeneous_a.pow 2).add isWeightedHomogeneous_b)
  · simpa using (((isWeightedHomogeneous_a.pow 6).add
      ((isWeightedHomogeneous_a.pow 3).mul isWeightedHomogeneous_c)).add
        (isWeightedHomogeneous_b.pow 3)).add (isWeightedHomogeneous_c.pow 2)

/-- **Item 2, prerequisite; Every `genAbs i` is itself `stdWeight`-
homogeneous, of degree `genAbsDeg i`. Uniform in `i`: no case split beyond what
`isWeightedHomogeneous_basisAbs` already supplies. -/
theorem isWeightedHomogeneous_genAbs (i : Fin 8) :
    IsWeightedHomogeneous stdWeight (genAbs i) (genAbsDeg i) := by
  fin_cases i <;> simp only [genAbs, genAbsDeg]
  · simpa [basisDeg] using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_cplusAbs).mul
      (isWeightedHomogeneous_basisAbs 0)
  · simpa [basisDeg] using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_cplusAbs).mul
      (isWeightedHomogeneous_basisAbs 1)
  · simpa [basisDeg] using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_cplusAbs).mul
      (isWeightedHomogeneous_basisAbs 2)
  · simpa [basisDeg] using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_cplusAbs).mul
      (isWeightedHomogeneous_basisAbs 3)
  · simpa [basisDeg] using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_cplusAbs).mul
      (isWeightedHomogeneous_basisAbs 4)
  · simpa [basisDeg] using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_cplusAbs).mul
      (isWeightedHomogeneous_basisAbs 5)
  · simpa [basisDeg] using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_cplusAbs).mul
      (isWeightedHomogeneous_basisAbs 6)
  · simpa [basisDeg] using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_cplusAbs).mul
      (isWeightedHomogeneous_basisAbs 7)

/-- **Item 2, discharged.** Each `genAbs i` expands in the 28 `standardMonomial`s with
`![4,6,7]`-homogeneous coefficients, by direct instantiation of `homogeneous_expand` at
`isWeightedHomogeneous_genAbs i`. No bundled `LinearMap`/dimension-count machinery needed. -/
theorem genAbs_standard_expand (i : Fin 8) :
    ∃ c : Fin 28 → Poly,
      (∀ j, IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (c j) (genAbsDeg i - stdDeg j)) ∧
        genAbs i = ∑ j, invariantEval (c j) * standardMonomial j :=
  homogeneous_expand (isWeightedHomogeneous_genAbs i)

end TernaryPeriodPolynomials.Argument.CharTwoKernel
