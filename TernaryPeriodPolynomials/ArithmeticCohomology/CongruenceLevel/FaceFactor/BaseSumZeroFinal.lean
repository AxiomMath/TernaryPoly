module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HomCuspValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.BaseSumZeroBridge

@[expose] public section


/-!
# `BaseSumZero`: the cusp values of homomorphisms `Γ(6) → ℚ` fill the sum-zero hyperplane (step (B))

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.GammaNFaceFactor

/-- **(B) at level 6, unconditionally**: `BaseSumZero` holds. -/
theorem baseSumZero : BaseSumZero :=
  baseSumZero_of_cusp_values (fun x hx => exists_hom_cusp_values (by norm_num : 3 ≤ 6) x hx)

end TernaryPeriodPolynomials.Argument.GammaNStokes
