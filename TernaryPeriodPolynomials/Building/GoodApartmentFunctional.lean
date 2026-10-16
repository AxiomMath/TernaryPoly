module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.IntegralDescent

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.GoodApartmentFunctional

theorem good_apartment_functional : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
    ∃ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F := by
  intro degree _positive polynomial solution
  exact IntegralSymbols.functional_of_rational_injective polynomial solution
    IntegralDescent.integralToRationalSymbols_injective

end TernaryPeriodPolynomials.GoodApartmentFunctional
