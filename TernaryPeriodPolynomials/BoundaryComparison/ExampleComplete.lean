module

public import TernaryPeriodPolynomials.ModularForm.Corollary14General

@[expose] public section


/-!
# The degree-ten Example and Corollary 1.4 for fields of every universe, in one statement each

Formalized by Claude Sonnet 5.5.

The targets `period_isomorphisms_and_finrank` and `example_degree_ten` quantify over `F : Type`.  `Exports/Corollary14General.lean` already
gives the universe-polymorphic `corollary_1_4_general` (all clauses, complex isomorphisms included, which live in `Type` anyway) and
`example_degree_ten_general` (first part only).  Here `example_degree_ten_complete` adds the second part of the Example (over `ℂ`, a
field of universe zero) so that the whole Example holds for `F : Type u` in a single declaration.
-/

open MvPolynomial TernaryPoly.Paper

universe u

namespace TernaryPeriodPolynomials.Argument.Statements

/-- **The degree-ten Example, complete, for every field `F : Type u` of characteristic zero.** -/
theorem example_degree_ten_complete :
    (∀ (F : Type u) [Field F] [CharZero F],
      symmetricTenPeriod F ∈ oddPeriodSpace F 10 ∧ alternatingTenPeriod F ∈ evenPeriodSpace F 10 ∧
      bind₁ ![X 1, X 0] (symmetricTenPeriod F) = symmetricTenPeriod F ∧
      bind₁ ![-X 0, X 1] (symmetricTenPeriod F) = -symmetricTenPeriod F ∧
      bind₁ ![X 0, -X 1] (symmetricTenPeriod F) = -symmetricTenPeriod F ∧
      bind₁ ![X 1, X 0] (alternatingTenPeriod F) = -alternatingTenPeriod F ∧
      bind₁ ![-X 0, X 1] (alternatingTenPeriod F) = alternatingTenPeriod F ∧
      bind₁ ![X 0, -X 1] (alternatingTenPeriod F) = alternatingTenPeriod F ∧
      LinearIndependent F ![symmetricTenSolution F, alternatingTenSolution F] ∧
      Submodule.span F {symmetricTenSolution F, alternatingTenSolution F} = solutionSpace F 10) ∧
    ∀ h : CuspForm levelOne 12, h ≠ 0 →
      (∃ c : ℂ, c ≠ 0 ∧ symmetricTenPeriod ℂ = c • oddPeriodPart 10 h) ∧
      (∃ c : ℂ, c ≠ 0 ∧ alternatingTenPeriod ℂ = c • normalizedEvenPeriodPart 10 h) :=
  ⟨fun F _ _ => example_degree_ten_general.{u} F, example_degree_ten.2⟩

end TernaryPeriodPolynomials.Argument.Statements
