module

public import TernaryPeriodPolynomials.Polynomial.RestrictionEquiv

@[expose] public section


/-!
# Corollary 1.4, third conjunct: vanishing at `n = 0` or odd `n`

For every characteristic-zero field `F` and every `n` with `n = 0 ∨ Odd n`, both
`symmetricSolutionSpace F n` and `alternatingSolutionSpace F n` are trivial.

Both spaces are submodules of `solutionSpace F n` (meet with an eigenspace condition), so
membership gives a homogeneous solution `f` of degree `n`. `TernaryPoly.Paper`'s
`TernaryPeriodPolynomials.Argument.RouteIndependent.solution_degree_zero_eq_zero` (`RouteIndependent/RestrictionEquivNew.lean`) and `TernaryPeriodPolynomials.Argument.Classification.solution_odd_eq_zero`
(`NewRoute/RestrictionNew.lean`)
show every homogeneous solution of degree `0`, resp. odd degree, vanishes outright, with no
eigenspace hypothesis needed. This is a direct citation, no new mathematics.
-/

open MvPolynomial TernaryPoly.Paper
open TernaryPeriodPolynomials.Argument.Classification TernaryPeriodPolynomials.Argument.RouteIndependent

namespace TernaryPeriodPolynomials.Argument.Corollary14

theorem symmetricSolutionSpace_eq_bot {F : Type*} [Field F] [CharZero F] {n : ℕ}
    (hn : n = 0 ∨ Odd n) : symmetricSolutionSpace F n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro f hf
  obtain ⟨hf', -⟩ := Submodule.mem_inf.mp hf
  obtain ⟨hh, hs⟩ := (mem_solutionSpace n f).mp hf'
  rcases hn with rfl | hodd
  · exact TernaryPeriodPolynomials.Argument.RouteIndependent.solution_degree_zero_eq_zero hh hs
  · exact TernaryPeriodPolynomials.Argument.Classification.solution_odd_eq_zero hh hs hodd

theorem alternatingSolutionSpace_eq_bot {F : Type*} [Field F] [CharZero F] {n : ℕ}
    (hn : n = 0 ∨ Odd n) : alternatingSolutionSpace F n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro f hf
  obtain ⟨hf', -⟩ := Submodule.mem_inf.mp hf
  obtain ⟨hh, hs⟩ := (mem_solutionSpace n f).mp hf'
  rcases hn with rfl | hodd
  · exact TernaryPeriodPolynomials.Argument.RouteIndependent.solution_degree_zero_eq_zero hh hs
  · exact TernaryPeriodPolynomials.Argument.Classification.solution_odd_eq_zero hh hs hodd

/-- **Corollary 1.4, third conjunct**, fully proved. -/
theorem conjunct3 : ∀ (F : Type) [Field F] [CharZero F] (n : ℕ), (n = 0 ∨ Odd n) →
    symmetricSolutionSpace F n = ⊥ ∧ alternatingSolutionSpace F n = ⊥ :=
  fun _F _ _ _n hn => ⟨symmetricSolutionSpace_eq_bot hn, alternatingSolutionSpace_eq_bot hn⟩

end TernaryPeriodPolynomials.Argument.Corollary14
