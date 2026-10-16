module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism
public import TernaryPeriodPolynomials.ModularForm.DegreeTen
public import TernaryPeriodPolynomials.Polynomial.RestrictionEquiv
public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange

@[expose] public section



/-!
# Universe-polymorphic forms of Corollary 1.4 and the degree-ten example

Formalized by Claude Sonnet 5.5.

The targets `period_isomorphisms_and_finrank` and `example_degree_ten` quantify over fields `F : Type`
(universe zero). The paper's statements are for every field of characteristic zero. This
module restates them for `F : Type u`, with no change to the targets: the dimension
statements are transported along coefficient base change from `ℚ`
(`TernaryPoly.Paper.*_finrank_baseChange`), the vanishing statements use the route-independent
mirrors of `Proofs/RouteIndependent/RestrictionEquivNew.lean`, and the example reuses the
universe-polymorphic proof pieces of `Proofs/CuspForms`.
-/

open MvPolynomial TernaryPoly.Paper
open TernaryPeriodPolynomials.Argument.Classification
open TernaryPeriodPolynomials.Argument.RouteIndependent

universe u

namespace TernaryPeriodPolynomials.Argument.Statements

/-- The homogeneous solution space of a field of characteristic zero vanishes in degree zero and
in odd degrees (route-independent). -/
theorem solutionSpace_eq_bot_of_zero_or_odd (F : Type u) [Field F] [CharZero F] (n : ℕ)
    (hn : n = 0 ∨ Odd n) : solutionSpace F n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  obtain ⟨hh, hsol⟩ := (mem_solutionSpace n f).mp hf
  rcases hn with rfl | hodd
  · exact TernaryPeriodPolynomials.Argument.RouteIndependent.solution_degree_zero_eq_zero hh hsol
  · exact TernaryPeriodPolynomials.Argument.Classification.solution_odd_eq_zero hh hsol hodd

/-- Dimensions of the solution spaces are independent of the field of characteristic zero and of
its universe: the Hilbert series of the rational solution spaces transfers to every field. -/
theorem hilbertSeries_transfer (F : Type u) [Field F] [CharZero F]
    (h : PowerSeries.mk (fun n => (Module.finrank ℚ (solutionSpace ℚ n) : ℤ)) *
        ((1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6)) = 2 * PowerSeries.X ^ 10) :
    PowerSeries.mk (fun n => (Module.finrank F (solutionSpace F n) : ℤ)) *
        ((1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6)) = 2 * PowerSeries.X ^ 10 := by
  have hc : (PowerSeries.mk (fun n => (Module.finrank F (solutionSpace F n) : ℤ))) =
      PowerSeries.mk (fun n => (Module.finrank ℚ (solutionSpace ℚ n) : ℤ)) := by
    congr 1
    funext n
    rw [solution_finrank_baseChange F n]
  rw [hc]
  exact h

/-- **Corollary 1.4** (`cor:dimensions`), for fields of arbitrary universe. For every even
`n > 0` the period maps induce complex linear isomorphisms `S_{n+2} ≅ W_n^{sym}(ℂ)` and
`S_{n+2} ≅ W_n^{alt}(ℂ)`. For every field `F : Type u` of characteristic zero and every `n ≥ 0`,
`dim_F W_n^{sym}(F) = dim_F W_n^{alt}(F) = dim_ℂ S_{n+2}`; the spaces
`W_n^{sym}(F)`, `W_n^{alt}(F)` and `W_n(F)` vanish when `n = 0` or `n` is odd; and
`∑_n dim_F W_n(F) tⁿ = 2t¹⁰ / ((1 - t⁴)(1 - t⁶))`. -/
theorem corollary_1_4_general :
    (∀ n : ℕ, 0 < n → Even n →
      (∃ e : CuspForm levelOne ((n : ℤ) + 2) ≃ₗ[ℂ] symmetricSolutionSpace ℂ n,
        ∀ h, (e h : MvPolynomial (Fin 3) ℂ) = cyclicLift (oddPeriodPart n h)) ∧
      (∃ e : CuspForm levelOne ((n : ℤ) + 2) ≃ₗ[ℂ] alternatingSolutionSpace ℂ n,
        ∀ h, (e h : MvPolynomial (Fin 3) ℂ) = cyclicLift (normalizedEvenPeriodPart n h))) ∧
    (∀ (F : Type u) [Field F] [CharZero F] (n : ℕ),
      Module.finrank F (symmetricSolutionSpace F n) =
          Module.finrank ℂ (CuspForm levelOne ((n : ℤ) + 2)) ∧
        Module.finrank F (alternatingSolutionSpace F n) =
          Module.finrank ℂ (CuspForm levelOne ((n : ℤ) + 2))) ∧
    (∀ (F : Type u) [Field F] [CharZero F] (n : ℕ), (n = 0 ∨ Odd n) →
      symmetricSolutionSpace F n = ⊥ ∧ alternatingSolutionSpace F n = ⊥ ∧
        solutionSpace F n = ⊥) ∧
    (∀ (F : Type u) [Field F] [CharZero F],
      PowerSeries.mk (fun n => (Module.finrank F (solutionSpace F n) : ℤ)) *
          ((1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6)) =
        2 * PowerSeries.X ^ 10) := by
  obtain ⟨h1, h2, -, h4⟩ := period_isomorphisms_and_finrank
  refine ⟨h1, ?_, ?_, fun F _ _ => hilbertSeries_transfer F (h4 ℚ)⟩
  · intro F _ _ n
    obtain ⟨hs, ha⟩ := h2 ℚ n
    exact ⟨(symmetricSolution_finrank_baseChange F n).trans hs,
      (alternatingSolution_finrank_baseChange F n).trans ha⟩
  · intro F _ _ n hn
    have hbot := solutionSpace_eq_bot_of_zero_or_odd F n hn
    exact ⟨eq_bot_mono (inf_le_left : symmetricSolutionSpace F n ≤ solutionSpace F n) hbot,
      eq_bot_mono (inf_le_left : alternatingSolutionSpace F n ≤ solutionSpace F n) hbot, hbot⟩

/-- **Degree-ten example, first part**, for fields of arbitrary universe: for every field `F` of
characteristic zero the period polynomials `q_s`, `q_a` satisfy the normalized period relations,
`q_s` is symmetric and odd in each variable, `q_a` is alternating and even in each variable, and
the cyclic sums `f_s = Φ(q_s)`, `f_a = Φ(q_a)` form a basis of `W₁₀(F)`. -/
theorem example_degree_ten_general (F : Type u) [Field F] [CharZero F] :
    symmetricTenPeriod F ∈ oddPeriodSpace F 10 ∧ alternatingTenPeriod F ∈ evenPeriodSpace F 10 ∧
      bind₁ ![X 1, X 0] (symmetricTenPeriod F) = symmetricTenPeriod F ∧
      bind₁ ![-X 0, X 1] (symmetricTenPeriod F) = -symmetricTenPeriod F ∧
      bind₁ ![X 0, -X 1] (symmetricTenPeriod F) = -symmetricTenPeriod F ∧
      bind₁ ![X 1, X 0] (alternatingTenPeriod F) = -alternatingTenPeriod F ∧
      bind₁ ![-X 0, X 1] (alternatingTenPeriod F) = alternatingTenPeriod F ∧
      bind₁ ![X 0, -X 1] (alternatingTenPeriod F) = alternatingTenPeriod F ∧
      LinearIndependent F ![symmetricTenSolution F, alternatingTenSolution F] ∧
      Submodule.span F {symmetricTenSolution F, alternatingTenSolution F} =
        solutionSpace F 10 :=
  ⟨symmetricTenPeriod_mem_oddPeriodSpace, alternatingTenPeriod_mem_evenPeriodSpace,
    symmetricTenPeriod_swap, symmetricTenPeriod_oddX, symmetricTenPeriod_oddY,
    alternatingTenPeriod_antiswap, alternatingTenPeriod_evenX, alternatingTenPeriod_evenY,
    linearIndependent_tenSolution F, solutionSpace_ten_eq_span F⟩

end TernaryPeriodPolynomials.Argument.Statements
