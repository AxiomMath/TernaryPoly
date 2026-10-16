module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.Building.Paths.Cocycle.Helpers

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.PolynomialPathCocycle

theorem polynomial_path_cocycle : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
    ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
    ∀ τ : rationalLevel → EdgeChains, IsPathFamily τ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        RealizesPathClass F τ c := by
  intro degree _ polynomial _ functional polynomialFunctional paths pathFamily
  exact ⟨Helpers.ambientPathCocycle functional paths pathFamily polynomialFunctional.1,
    Helpers.ambientPathCocycle_realizes functional paths pathFamily polynomialFunctional.1⟩

end TernaryPeriodPolynomials.PolynomialPathCocycle
