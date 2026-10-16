module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Lemma53Assembly

@[expose] public section


/-! Target: Lemma 5.3 (`mf:lem:kernel`) of the paper. -/

open MvPolynomial

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Lemma 5.3.** Over `k = 𝔽₂`, the ring `R = k[d₄, d₆, d₇]` is a polynomial ring, and on
symmetric polynomials `ker N̄` is a free `R`-module on `K_j = a c₊ B_j`, `0 ≤ j < 8`: a symmetric
`g` satisfies `N̄ g = 0` exactly when it has a unique expansion `g = ∑_j r_j(d₄, d₆, d₇) K_j`. -/
theorem charTwo_normKernel_free :
    AlgebraicIndependent (ZMod 2)
      ![TernaryPoly.CharTwoNorm.d4, TernaryPoly.CharTwoNorm.d6, TernaryPoly.CharTwoNorm.d7] ∧
    ∀ g : Poly2, g.IsSymmetric →
      (TernaryPoly.CharTwoNorm.norm g = 0 ↔
        ∃! r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2),
          g = ∑ j, TernaryPoly.CharTwoNorm.invariantEval (r j) *
            TernaryPoly.CharTwoNorm.generator j) := by
  exact ⟨TernaryPeriodPolynomials.Argument.CharTwoKernel.lemma_5_3_conjunct1,
    TernaryPeriodPolynomials.Argument.CharTwoKernel.lemma_5_3_conjunct2⟩

end TernaryPeriodPolynomials
