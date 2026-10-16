module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.DegreeOneVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.DegreeTwoVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.DirectFinal

@[expose] public section


/-! Proof of the inner bad-line cuspidal span child.

Degrees `n = 1, 2` are closed unconditionally: every good-vanishing inner bad-line class is
zero there (`InnerCuspidalArithmetic.DegreeOneVanishing.inner_bad_line_degree_one_zero` and
`DegreeTwoVanishing.inner_bad_line_degree_two_zero`, the Sol reference implementation, AxiomCode).
For `n ≥ 3` the inner bad-line classes are the cuspidal cohomology of the level-three Levi,
which is nonzero (weight `n + 3` cusp forms on `Γ₁(3)`); that branch is
`Automorphic.DirectFinal.inner_bad_line_n_plus_three_final` (AxiomCode, Claude Sonnet 5.5): Eichler–Shimura at level three (Opus 5.5), adelic lifts of eigenforms, and a direct comparison of an inner class with an automorphic line class through the
injective bad-line edge map on the radical kernel.
-/

open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials

theorem inner_bad_line_cuspidal_span : ∀ n : ℕ, 0 < n → ∀ a : StratumH2 n trivialCharacter .line,
    VanishesOnGood n trivialCharacter .line a → InnerBoundary n trivialCharacter .line a →
    a ∈ automorphicLineSpan n := by
  intro n hn a good inner
  open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic in
  match n, hn, a, good, inner with
  | 1, _, a, good, inner =>
    rw [DegreeOneVanishing.inner_bad_line_degree_one_zero a good inner]
    exact Submodule.zero_mem _
  | 2, _, a, good, inner =>
    rw [DegreeTwoVanishing.inner_bad_line_degree_two_zero a good inner]
    exact Submodule.zero_mem _
  | n + 3, _, a, good, inner =>
    exact TernaryPeriodPolynomials.Automorphic.DirectFinal.inner_bad_line_n_plus_three_final
      n a good inner

end TernaryPeriodPolynomials
