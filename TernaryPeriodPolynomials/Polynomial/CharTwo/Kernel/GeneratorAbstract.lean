module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Bridge

@[expose] public section





open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

/-! The abstract (`DicksonQuotient`-side) mirror of `TernaryPoly.CharTwoNorm.generator`, and the
transport of generator-independence to the abstract copy via the `Bridge` lemmas. -/

open TernaryPoly.DicksonQuotient (a b c)

/-- Abstract mirror of `TernaryPoly.CharTwoNorm.cplus`. -/
noncomputable def cplusAbs : TernaryPoly.DicksonQuotient.Poly := a * b + c

/-- Abstract mirror of `TernaryPoly.CharTwoNorm.basis`. -/
noncomputable def basisAbs : Fin 8 → TernaryPoly.DicksonQuotient.Poly :=
  ![1, a, a ^ 2 + b, a * b, a ^ 3 + c, a * cplusAbs, a ^ 3 * (a ^ 2 + b),
    a ^ 6 + a ^ 3 * c + b ^ 3 + c ^ 2]

/-- Abstract mirror of `TernaryPoly.CharTwoNorm.generator`. -/
noncomputable def genAbs (i : Fin 8) : TernaryPoly.DicksonQuotient.Poly := a * cplusAbs * basisAbs i

theorem elementaryEval_dickson_cplus :
    TernaryPoly.CharTwoNorm.elementaryEval cplusAbs = TernaryPoly.CharTwoNorm.cplus := by
  simp [cplusAbs, TernaryPoly.CharTwoNorm.cplus, elementaryEval_dickson_a,
    elementaryEval_dickson_b, elementaryEval_dickson_c]

theorem elementaryEval_dickson_basisAbs (i : Fin 8) :
    TernaryPoly.CharTwoNorm.elementaryEval (basisAbs i) = TernaryPoly.CharTwoNorm.basis i := by
  fin_cases i <;>
    simp [basisAbs, TernaryPoly.CharTwoNorm.basis, elementaryEval_dickson_a,
      elementaryEval_dickson_b, elementaryEval_dickson_c, elementaryEval_dickson_cplus]

theorem elementaryEval_genAbs (i : Fin 8) :
    TernaryPoly.CharTwoNorm.elementaryEval (genAbs i) = TernaryPoly.CharTwoNorm.generator i := by
  simp [genAbs, TernaryPoly.CharTwoNorm.generator, elementaryEval_dickson_a,
    elementaryEval_dickson_cplus, elementaryEval_dickson_basisAbs]

theorem elementaryEval_sum_invariantEval_mul_genAbs (p : Fin 8 → TernaryPoly.DicksonQuotient.Poly) :
    TernaryPoly.CharTwoNorm.elementaryEval
        (∑ i, TernaryPoly.DicksonQuotient.invariantEval (p i) * genAbs i) =
      ∑ i, TernaryPoly.CharTwoNorm.invariantEval (p i) * TernaryPoly.CharTwoNorm.generator i := by
  rw [elementaryEval_sum_invariantEval_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [elementaryEval_genAbs]

/-- **Main transport lemma.** For arbitrary coefficients `p : Fin 8 → Poly` (the same underlying
type on both sides), the real `generator`-combination vanishes iff the abstract `genAbs`-
combination (same coefficients, pushed through `DicksonQuotient.invariantEval`) vanishes. This
reduces uniqueness in `charTwo_normKernel_free` entirely to an independence statement inside the clean abstract
copy `TernaryPoly.DicksonQuotient.Poly`. -/
theorem sum_invariantEval_mul_generator_eq_zero_iff
    (p : Fin 8 → TernaryPoly.DicksonQuotient.Poly) :
    (∑ i, TernaryPoly.CharTwoNorm.invariantEval (p i) * TernaryPoly.CharTwoNorm.generator i = 0) ↔
      (∑ i, TernaryPoly.DicksonQuotient.invariantEval (p i) * genAbs i = 0) := by
  rw [← elementaryEval_sum_invariantEval_mul_genAbs]
  constructor
  · intro h
    exact TernaryPoly.CharTwoNorm.elementaryEval_injective (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

end TernaryPeriodPolynomials.Argument.CharTwoKernel
