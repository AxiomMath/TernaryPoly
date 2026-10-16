module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.Building.Paths.GoodCusps.Paths

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.PolynomialPathGoodCusps

theorem polynomial_path_good_cusps : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
    ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
    ∀ (τ : rationalLevel → EdgeChains)
      (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
    IsPathFamily τ → RealizesPathClass F τ c →
    GoodBoundaryVanishing n trivialCharacter (globalCoordinates n trivialCharacter c) := by
  intro n _ f _ F functional_valid τ c paths_valid realizes
  exact ⟨Helpers.vanishesOnGood_path functional_valid paths_valid realizes .plane,
    Helpers.vanishesOnGood_path functional_valid paths_valid realizes .line⟩

end TernaryPeriodPolynomials.PolynomialPathGoodCusps

