module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.Building.Paths.Independence.Helpers

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.PolynomialPathIndependence

theorem polynomial_path_independence : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
    ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
    ∀ (τ : rationalLevel → EdgeChains)
      (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
    IsPathFamily τ → RealizesPathClass F τ c →
    ∀ τ' c', IsPathFamily τ' → RealizesPathClass F τ' c' →
      classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c' = classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c := by
  intro degree _ polynomial _ functionalMap functional first first_cocycle first_path first_realizes
    second second_cocycle second_path second_realizes
  obtain ⟨cochain, boundary_eq⟩ := Helpers.boundary_of_subgroup_boundary
    rationalLevel (rationalCoefficientComponent degree trivialCharacter)
    (second_cocycle - first_cocycle) (Helpers.pathPrimitive functionalMap second first)
    (Helpers.pathPrimitive_equivariant functionalMap second first)
    (Helpers.pathPrimitive_boundary functionalMap functional second first second_path first_path
      second_cocycle first_cocycle second_realizes first_realizes)
  change Submodule.Quotient.mk second_cocycle = Submodule.Quotient.mk first_cocycle
  exact (Submodule.Quotient.eq _).2 ⟨cochain, boundary_eq⟩

end TernaryPeriodPolynomials.PolynomialPathIndependence
