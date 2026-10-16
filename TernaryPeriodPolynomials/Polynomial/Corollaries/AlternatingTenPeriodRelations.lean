module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Restriction

@[expose] public section


/-! Period relations for `alternatingTenPeriod`, the missing analogue of
`symmetricTenPeriod_periodRelations_pc` (already proved in `PositiveCharacteristic.lean`) needed to
instantiate Corollary 1.5's universal hypothesis at `alternatingTenSolution F`
(see `Corollary15PartB.lean`). -/


open MvPolynomial TernaryPoly TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument

-- each of the four conjuncts reduces, after unfolding `bind₁` through the degree-ten formula
-- `X0^2*X1^2*(X0^2-X1^2)^3`, to a `ring`-provable two-variable polynomial identity.
theorem alternatingTenPeriod_periodRelations_pc (K : Type*) [CommRing K] :
    PeriodRelations (alternatingTenPeriod K) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [alternatingTenPeriod, map_mul, map_sub, map_pow, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring1
  · simp only [alternatingTenPeriod, map_mul, map_sub, map_pow, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring1
  · simp only [alternatingTenPeriod, map_mul, map_sub, map_pow, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring1
  · simp only [alternatingTenPeriod, map_mul, map_sub, map_pow, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring1

/-- `alternatingTenSolution` is a solution. -/
theorem alternatingTenSolution_solution (K : Type*) [CommRing K] :
    Solution (alternatingTenSolution K) :=
  cyclicLift_solution (alternatingTenPeriod_periodRelations_pc K)

end TernaryPeriodPolynomials.Argument
