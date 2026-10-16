module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.FaceCan

@[expose] public section


/-!
# Finite-index induction for the canonical cuspidal pairing of `Γ(N)`

Paper: `ar:eq:facepair`; Step 2 of the literal Stokes lemma at `Γ(N)`.

* `cuspidal_pairing_ind`: for `Γ(M) ≤ Γ(N)` (`N, M ≥ 3`), finite-dimensional `Γ(N)`-modules `V, V'` with a perfect invariant pairing `e`, the induced modules `Fun(Γ(N)/Γ(M), V)`, `Fun(Γ(N)/Γ(M), V')`
  with the summed pairing, and any pairings `B_N`, `B_M` with the cup-form property, `B_N x y = B_M (shapiro x) (shapiro y)` on cuspidal classes.
* `cupForm_eq_of_ind`: the underlying identity of cup forms.
* `isCupPairing_facePairingCan`: the `facePairingCan` has the cup-form property.

This is the `Γ₂`-level (Farey/cusp) half of `OrbitIdentLine/OrbitIdentPlane`; the radical-level Shapiro and Mackey orbit decomposition are not part of it.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.CuspidalInduction

open TernaryPeriodPolynomials.Argument.CuspidalInduction

export TernaryPeriodPolynomials.Argument.CuspidalInduction
  (cuspidal_pairing_ind cupForm_eq_of_ind isCupPairing_facePairingCan IsCupPairing shapiroCusp indRep eInd)

end TernaryPeriodPolynomials.Argument.Statements.CuspidalInduction
