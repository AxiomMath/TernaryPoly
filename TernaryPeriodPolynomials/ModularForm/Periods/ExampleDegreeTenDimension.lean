module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Classification
public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodDimension

@[expose] public section



/-!
# The dimension of `oddPeriodSpace F 10` is exactly one

This composes three already-proved facts in the pre-existing library:

* `TernaryPoly.Paper.oddPeriodSpace_eq F n : oddPeriodSpace F n = BinaryComplexPeriod.space F n`
  (for `Field F` `[CharZero F]`), from `TernaryPeriodPolynomials/Polynomial/Classification.lean`;
* `TernaryPoly.BinaryComplexPeriod.rational_finrank d hd :
  Module.finrank ℚ (space ℚ d) = (d+2)/4 - (d/6+1)`, from `TernaryPeriodPolynomials/PeriodPolynomial/BinaryPeriodDimension.lean`;
* `TernaryPoly.Paper.oddPeriod_finrank_baseChange A n :
  Module.finrank A (oddPeriodSpace A n) = Module.finrank ℚ (oddPeriodSpace ℚ n)`
  (for `[CommRing A] [Algebra ℚ A] [Nontrivial A]`), from
  `TernaryPeriodPolynomials/Polynomial/CoefficientBaseChange.lean`.

No analogous bridge for `evenPeriodSpace` (the alternating side); only the odd side is bridged.



-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument

open TernaryPoly.Paper

theorem oddPeriodSpace_ten_finrank_eq_one
    (F : Type*) [Field F] [CharZero F] :
    Module.finrank F (oddPeriodSpace F 10) = 1 := by
  rw [oddPeriod_finrank_baseChange F 10, oddPeriodSpace_eq ℚ 10,
    TernaryPoly.BinaryComplexPeriod.rational_finrank 10 (by decide)]

end TernaryPeriodPolynomials.Argument
