module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity.Helpers

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.LevelOneCohomologicalParity

theorem level_one_cohomological_parity : ∀ n : ℕ, 0 < n → ∀ D : InducingData n, D.chi = trivialCharacter →
    SphericalCusp D.cusp → Odd n := by
  intro degree _ inducing _ spherical
  exact Helpers.cohomological_spherical_odd degree inducing.cusp
    inducing.cohomological spherical

end TernaryPeriodPolynomials.LevelOneCohomologicalParity
