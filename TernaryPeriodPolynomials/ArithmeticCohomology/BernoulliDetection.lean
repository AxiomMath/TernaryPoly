module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Detection

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection

theorem polynomial_bernoulli_detection : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
    ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
    ∀ (τ : rationalLevel → EdgeChains)
      (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
    IsPathFamily τ → RealizesPathClass F τ c →
    NormalizedBadLine f c →
      (globalCoordinates n trivialCharacter c).2 = 0 → bernoulliObstruction f = 0 := by
  intro degree _ polynomial symmetric _ _ _ cocycle _ _ normalized vanishing
  exact Helpers.normalized_bernoulli_detection polynomial symmetric cocycle normalized vanishing

end TernaryPeriodPolynomials.PolynomialBernoulliDetection
