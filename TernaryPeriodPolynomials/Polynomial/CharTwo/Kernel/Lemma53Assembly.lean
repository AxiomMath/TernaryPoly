module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.LemmaA
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.AlgIndependence
public import TernaryPeriodPolynomials.Polynomial.CharTwo.FullKernel

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial

/-! Final assembly of Lemma 5.3 (`mf:lem:kernel`) from the pieces proved elsewhere:

* Conjunct 1 (`d4,d6,d7` algebraically independent) is `lemma_5_3_conjunct1`, from
  `AlgIndependence.lean`.
* Conjunct 2's existence half (and the easy backward direction) is
  `TernaryPoly.CharTwoNorm.norm_kernel_iff_expansion`.
* The `g.IsSymmetric` hypothesis (standard Mathlib `MvPolynomial.IsSymmetric`) is converted to the
  `CharTwoProjector.Symmetric` form that lemma needs via
  `TernaryPoly.CharTwoProjector.symmetric_iff_isSymmetric` (imported transitively here via `Bridge.lean`).
* Conjunct 2's uniqueness half is new: `generator_injective` below transports `lemma_A`
  (`LemmaA.lean`, proved in the abstract `TernaryPoly.DicksonQuotient` copy) to the real
  `TernaryPoly.CharTwoNorm` copy via the bridge transport lemma
  `sum_invariantEval_mul_generator_eq_zero_iff` (`GeneratorAbstract.lean`, imported transitively
  via `LemmaA.lean`). -/


/-- **Injectivity of the real generator-coefficient map.** The only way a `CharTwoNorm.invariantEval`-
combination of the real generators `CharTwoNorm.generator` can vanish is if every coefficient does.
Transported from the abstract `lemma_A` through `sum_invariantEval_mul_generator_eq_zero_iff`. -/
theorem generator_injective (p : Fin 8 → MvPolynomial (Fin 3) (ZMod 2))
    (hsum : ∑ i, TernaryPoly.CharTwoNorm.invariantEval (p i) *
      TernaryPoly.CharTwoNorm.generator i = 0) : ∀ i, p i = 0 :=
  lemma_A p ((sum_invariantEval_mul_generator_eq_zero_iff p).mp hsum)


/-- **Lemma 5.3, conjunct 2.** For symmetric `g`, `norm g = 0` iff `g` has a unique expansion
`g = ∑ j, invariantEval (r j) * generator j`. -/
theorem lemma_5_3_conjunct2 :
    ∀ g : MvPolynomial (Fin 3) (ZMod 2), g.IsSymmetric →
      (TernaryPoly.CharTwoNorm.norm g = 0 ↔
        ∃! r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2),
          g = ∑ j, TernaryPoly.CharTwoNorm.invariantEval (r j) *
            TernaryPoly.CharTwoNorm.generator j) := by
  intro g hg
  have hs : TernaryPoly.CharTwoProjector.Symmetric g :=
    (TernaryPoly.CharTwoProjector.symmetric_iff_isSymmetric g).mpr hg
  constructor
  · intro hn
    obtain ⟨q, hq⟩ := (TernaryPoly.CharTwoNorm.norm_kernel_iff_expansion hs).mp hn
    refine ⟨q, hq, ?_⟩
    intro r hr
    have hdiff : ∑ j, TernaryPoly.CharTwoNorm.invariantEval (r j - q j) *
        TernaryPoly.CharTwoNorm.generator j = 0 := by
      have heq :
          ∑ j, TernaryPoly.CharTwoNorm.invariantEval (r j) * TernaryPoly.CharTwoNorm.generator j =
            ∑ j, TernaryPoly.CharTwoNorm.invariantEval (q j) * TernaryPoly.CharTwoNorm.generator j := by
        rw [← hr, ← hq]
      simp only [map_sub, sub_mul]
      rw [Finset.sum_sub_distrib, heq, sub_self]
    funext j
    exact sub_eq_zero.mp (generator_injective (fun k => r k - q k) hdiff j)
  · rintro ⟨r, hr, -⟩
    rw [hr]
    exact TernaryPoly.CharTwoNorm.norm_sum_invariantEval_mul_generator r

end TernaryPeriodPolynomials.Argument.CharTwoKernel
