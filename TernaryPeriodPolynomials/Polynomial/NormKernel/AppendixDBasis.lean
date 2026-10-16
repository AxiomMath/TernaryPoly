module

public import TernaryPeriodPolynomials.Polynomial.NormKernel.LiftedBasis

@[expose] public section


/-!
# Appendix D (`mf:app:kernel`): the unnumbered basis claims

In `S = 𝔽₂[a, b, c]` (weights 1, 2, 3) with `I = (d₄, d₆, d₇)`:

* the fourteen printed monic polynomials form a Gröbner basis of `I` for lex `a > b > c`, with the
  printed leading monomials (`groebner_basis`);
* the standard monomials are exactly the 28 printed ones, and their residue classes are a basis of
  `S/I` (`standard_monomials`, `quotient_basis`);
* `NF_I` (the remainder on division by the Gröbner basis) of `K₀, …, K₇` and of `(1 + π)m`, `m ∈ 𝓜`,
  are the printed ones (`normal_forms_K`, `normal_forms_onePlusProjector`), and the residue classes
  of `K₀, …, K₇, (1 + π)m` form another basis of `S/I` (`adapted_quotient_basis`);
* the 28 homogeneous lifts form an `R`-basis of `S`, `R = 𝔽₂[d₄, d₆, d₇]`, with the printed Hilbert
  generating polynomial (`lifted_basis`, `lifted_hilbert`); `d₄, d₆, d₇` are algebraically
  independent (`CharTwoKernel.lemma_5_3_conjunct1`).

Written by Claude Opus 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.AppendixDBasis

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly standardMonomial dicksonIdeal invariantEval)
open TernaryPeriodPolynomials.Argument.AppendixD
open TernaryPeriodPolynomials.Argument.CharTwoKernel (genAbs stdDeg stdWeight)

/-- **The printed Gröbner basis.** -/
theorem groebner_basis :
    IsGroebnerBasis MonomialOrder.lex groebnerBasis dicksonIdeal ∧
      (∀ i, MonomialOrder.lex.leadingCoeff (groebnerBasis i) = 1) ∧
      (∀ i, MonomialOrder.lex.degree (groebnerBasis i) = e3t (lmTriple i)) :=
  ⟨groebnerBasis_isGroebner, leadingCoeff_groebnerBasis, degree_groebnerBasis⟩

/-- **The standard monomials.** -/
theorem standard_monomials (e : Fin 3 →₀ ℕ) :
    (∀ i : Fin 14, ¬ MonomialOrder.lex.degree (groebnerBasis i) ≤ e) ↔
      ∃ k : Fin 28, e = e3t (stdTriple k) :=
  standard_iff e

/-- **A basis of `S/I`: the 28 standard monomials.** -/
theorem quotient_basis (k : Fin 28) :
    quotientBasis k = Ideal.Quotient.mk dicksonIdeal (standardMonomial k) :=
  quotientBasis_apply k

/-- **`NF_I` is the division remainder.** -/
theorem normal_form_eq_remainder (f r : Poly) (q : Fin 14 →₀ Poly)
    (hfr : f = Finsupp.linearCombination Poly groebnerBasis q + r)
    (hsupp : ∀ e ∈ r.support, ∀ i : Fin 14, ¬ MonomialOrder.lex.degree (groebnerBasis i) ≤ e) :
    r = nf f :=
  remainder_eq_nf f r q hfr hsupp

/-- **The printed table `NF_I(Kⱼ)`.** -/
theorem normal_forms_K (j : Fin 8) : nf (genAbs j) = printedNFK j := by
  fin_cases j
  · exact nf_K_0
  · exact nf_K_1
  · exact nf_K_2
  · exact nf_K_3
  · exact nf_K_4
  · exact nf_K_5
  · exact nf_K_6
  · exact nf_K_7

/-- **The printed table `NF_I((1 + π)m)`**: `m` itself except in the five printed cases. -/
theorem normal_forms_onePlusProjector :
    (∀ t : Fin 5, nf (standardMonomial (excIndex t) + projS (standardMonomial (excIndex t))) =
      printedNFExc t) ∧
    ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 14, 17, 22, 25, 27} : Finset (Fin 28)),
      nf (standardMonomial i + projS (standardMonomial i)) = standardMonomial i := by
  refine ⟨fun t => ?_, fun i hi => ?_⟩
  · fin_cases t
    · exact nf_exc_0
    · exact nf_exc_1
    · exact nf_exc_2
    · exact nf_exc_3
    · exact nf_exc_4
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact nf_onePlusProjector_0
    · exact nf_onePlusProjector_1
    · exact nf_onePlusProjector_2
    · exact nf_onePlusProjector_3
    · exact nf_onePlusProjector_4
    · exact nf_onePlusProjector_5
    · exact nf_onePlusProjector_6
    · exact nf_onePlusProjector_7
    · exact nf_onePlusProjector_8
    · exact nf_onePlusProjector_10
    · exact nf_onePlusProjector_14
    · exact nf_onePlusProjector_17
    · exact nf_onePlusProjector_22
    · exact nf_onePlusProjector_25
    · exact nf_onePlusProjector_27

/-- **The basis of `S/I` adapted to the projector.** -/
theorem adapted_quotient_basis (k : Fin 28) :
    adaptedBasis k = Ideal.Quotient.mk dicksonIdeal (adapted k) :=
  adaptedBasis_apply k

/-- **The lifted `R`-basis of `S`.** -/
theorem lifted_basis (f : Poly) :
    ∃! p : Fin 28 → Poly, f = ∑ k, invariantEval (p k) * adapted k :=
  adapted_expansion_existsUnique f

/-- **The Hilbert generating polynomial of the lifts.** -/
theorem lifted_hilbert :
    (∀ k, IsWeightedHomogeneous stdWeight (adapted k) (stdDeg k)) ∧
      (∑ k : Fin 28, PowerSeries.X ^ (stdDeg k) : PowerSeries ℤ) *
          ((1 - PowerSeries.X ^ 1) * (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X ^ 3)) =
        (1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6) * (1 - PowerSeries.X ^ 7) :=
  adapted_hilbert

/-- **The projector vanishes on the lifts `(1 + π)m`.** -/
theorem projector_onePlus_zero (f : Poly) : projS (f + projS f) = 0 := projS_onePlus f

end TernaryPeriodPolynomials.Argument.Statements.AppendixDBasis
