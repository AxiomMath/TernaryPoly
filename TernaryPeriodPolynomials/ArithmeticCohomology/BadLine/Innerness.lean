module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.AllFlags

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness

theorem polynomial_bad_line_innerness : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
    ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
    ∀ (τ : rationalLevel → EdgeChains)
      (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
    IsPathFamily τ → RealizesPathClass F τ c →
    NormalizedBadLine f c →
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 := by
  intro n positive f solution F functional paths c path_family realization normalized
  exact Helpers.innerBoundary_of_stabilizer_primitives n trivialCharacter .line c
    (Helpers.normalizedPathClass_all_flag_primitives n positive f solution F functional paths c
      path_family realization normalized)

end TernaryPeriodPolynomials.PolynomialBadLineInnerness
