module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Primitive
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.HermiteCount
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.HNF
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.Cyclic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.Functional
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.CyclicCount
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.IntegralSubstitution
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Identity

@[expose] public section


/-!
# Lattice counts behind the unramified factors (Appendix C)

Formalized by Claude Haiku 5.5.
Paper: Appendix C.

Standalone finite counting statements, each proved in `Revision/Proofs/LatticeCounts`:

* `primPairs`, `PrimPt`
  (pairs not both divisible by `p`), the free unit action `primUnitAction`, the orbit size `p^r - p^(r-1) = (1 - p⁻¹) p^r`
  and the orbit count `p^r + p^(r-1)`.
* counts of Hermite normal form
  triples `(a, b, d)` with `a d = p^r`, `0 ≤ b < d`, cyclic iff `gcd(a, b, d) = 1`.
* The Hermite bijection (`Proofs/LatticeCounts/LatticeHNF.lean`): `hnfEquiv` identifies the triples of level `n` with the
  subgroups of `ℤ²` of index `n`, so the counts are counts of sublattices (`card_index_subgroups`).
* Cyclicity of `ℤ²/Λ` (`Proofs/LatticeCounts/LatticeCyclic.lean`): `ℤ²/Λ` is cyclic iff `gcd(a, b, d) = 1`.
* The sublattices `Λ_{s,t}` of primitive pairs (`Proofs/LatticeCounts/LatticeFunctional.lean`) and the cyclic
  count `p^r + p^(r-1)` of sublattices (`Proofs/LatticeCounts/LatticeCyclicCount.lean`).
* the matrix `k₀` over `ℚ_[p]`
  with `p`-integral entries, `det k₀ = 1`, and `L(s,t) k₀ = [[A, *], [0, p^{-r}]]`.
* the algebraic identity
  `c_p = (1 - a t/p + q t²/p²)/(1 - a t + q t²)` and the count `Nat.card (PrimPt p r) = p^(2r) - p^(2r-2)`.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.LatticeCounts

open TernaryPeriodPolynomials.Argument.LatticeCounts

alias primitive_pairs_card := card_primPt
alias primitive_unit_action_free := primUnitAction_free
alias primitive_orbit_card := primOrbit_card
alias primitive_orbit_card_rat := primOrbit_card_rat
alias primitive_orbit_count := primOrbit_count
alias hermite_triples_card := card_hnfData
alias cyclic_hermite_card := card_cyclicHNF
alias noncyclic_hermite_card_level := card_nonCyclicHNF
alias noncyclic_hermite_card_index := card_nonCyclicHNF_eq_hnfData
alias lattice_of_triple := latOf
alias lattice_row_span := latZ
alias mem_lattice_row_span := mem_latZ
alias index_lattice_of_triple := index_latOf
alias hermite_triple_equiv_lattices := hnfEquiv
alias index_lattices_card := card_index_subgroups
alias gcd_eq_one_iff_prime := gcd_eq_one_iff_prime
alias cyclic_quotient_iff_gcd := isAddCyclic_quot_latZ_iff
alias cyclic_quotient_iff_gcd_triple := isAddCyclic_quot_latOf_iff
alias lattice_pair_phi := phiST
alias lattice_pair := lamST
alias lattice_pair_index_cyclic := index_and_cyclic_lamST
alias cyclic_lattice_is_pair := exists_lamST_of_cyclic
alias lattice_pair_eq_iff_unit := lamST_eq_iff
alias primitive_fiber_card := card_fiber_lamST
alias primitive_fiber_card_rat := card_fiber_lamST_rat
alias cyclic_index_lattices_card := card_cyclic_index_subgroups
alias integral_substitution_matrix := substitution_matrix
alias integral_substitution_exists := exists_substitution_matrix
alias integral_substitution_integral := substK_integral
alias integral_substitution_det := substK_det
alias integral_substitution_L_mul := substL_mul_substK
alias bezout_of_max_norm := exists_bezout_of_max
alias shell_identity_relations := shell_identity_of_relations
alias shell_identity_closed_form := local_factor_closed_form
alias shell_count := card_shell_primPt
alias shell_count_closed := card_shell_primPt_eq

end TernaryPeriodPolynomials.Argument.Statements.LatticeCounts
