module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.OuterRatioProduct
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.OuterLBridge
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.OuterLimit

@[expose] public section


/-!
# Global outer step and the `L^{(3)} = E_3 · L` normalisation

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

* `Proofs/LatticeCounts/OuterRatioProduct.lean`: `outer_ratio_product`, the absolute convergence of the
  local Euler ratios over the primes `p ≠ 3` and their product `L^{(3)}(h,k-2) / L^{(3)}(h,k-1)`.
* `Proofs/LatticeCounts/GlobalOuterLimit.lean`: `global_integral_eq_outer_ratio`, the limit step: a finite-`S` identity
  together with convergence of the finite-`S` integrals gives the global value as `v_h` times the outer ratio.
* `Proofs/LatticeCounts/OuterLBridge.lean`: `removed_L_eq_euler_mul_full`, `L^{(3)}(h,s) = E_3(s) · L(h,s)`,
  and `global_entry_ratio_removed_eq`, the identification with the normalisation of Appendix C.6.

This file only renames these declarations; the proofs are in the modules above.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.LatticeCountsGlobal

alias outer_ratio_product := TernaryPeriodPolynomials.Argument.outer_ratio_product
alias removed_L_eq_euler_mul_full := TernaryPeriodPolynomials.Argument.removed_L_eq_euler_mul_full
alias global_entry_ratio_removed_eq := TernaryPeriodPolynomials.Argument.global_entry_ratio_removed_eq
alias global_integral_eq_outer_ratio := TernaryPeriodPolynomials.Argument.global_integral_eq_outer_ratio

end TernaryPeriodPolynomials.Argument.Statements.LatticeCountsGlobal
