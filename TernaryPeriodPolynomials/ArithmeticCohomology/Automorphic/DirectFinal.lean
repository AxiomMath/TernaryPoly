module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Interfaces
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Period.InnerEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Period.MemberRealized
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Covers

@[expose] public section


/-!
# The `n + 3` branch of `inner_bad_line_cuspidal_span`, unconditionally

The assembly of the direct route (`DirectRoute`, `Contracts`):

* `Period.InnerEdge.innerEdgeRealized`: the edge class of the bad-line coordinate of
  every inner bad-line class is `n + 1` times a period class;
* `Period.MemberRealized.memberRealized` (with EIa): for every cohomological cuspidal
  datum, the cusp form of each classical level-three weight vector has its period class realized
  by the automorphic line span;
* `Constituent.modelCoversForms` (with the constituent chain WG, PL1, PL2, TB1, TB2, COH): the cusp forms of the level-three weight vectors of the cuspidal constituents of the
  Bergman model of the adelic lifts span all cusp forms of weight `n + 3` for `Γ₁(3)`.

`directInputs` is `DirectRoute.DirectInputs n`; `inner_bad_line_n_plus_three_final` is the goal of
the `n + 3` branch.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open GeneralEisenstein
open Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.Automorphic.DirectFinal

open TernaryPeriodPolynomials.Automorphic.DirectRoute
open TernaryPeriodPolynomials.Automorphic.Contracts

/-- **The two inputs of the direct route hold for every degree `n + 3`.** -/
theorem directInputs (n : ℕ) : DirectInputs n :=
  ⟨Period.InnerEdge.innerEdgeRealized (n + 3) (Nat.succ_pos _),
    periodsRealized_of (n + 3) (Nat.succ_pos _)
      (fun D => Period.MemberRealized.memberRealized (n + 3) (Nat.succ_pos _) D)
      (Constituent.modelCoversForms (n + 3) (by omega))⟩

/-- **The goal at the `n + 3` branch of `inner_bad_line_cuspidal_span`.** -/
theorem inner_bad_line_n_plus_three_final (n : ℕ)
    (a : StratumH2 (n + 3) trivialCharacter .line)
    (good : VanishesOnGood (n + 3) trivialCharacter .line a)
    (inner : InnerBoundary (n + 3) trivialCharacter .line a) :
    a ∈ automorphicLineSpan (n + 3) :=
  inner_bad_line_n_plus_three (directInputs n) a good inner

end TernaryPeriodPolynomials.Automorphic.DirectFinal
