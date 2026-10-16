module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryHeckeDescent.Helpers

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.BoundaryHeckeDescent

theorem boundary_hecke_descent : ∀ (n : ℕ) (χ : RankOneCharacter),
    ∃ hecke : BoundaryHecke n χ, ActualBoundaryHecke n χ hecke := by
  intro degree character
  refine ⟨fun side => Helpers.cohomologyAction
    (flagRepresentation (rationalCoefficientComponent degree character) side), ?_⟩
  intro side
  exact Helpers.cohomologyAction_realizes
    (flagRepresentation (rationalCoefficientComponent degree character) side)

end TernaryPeriodPolynomials.BoundaryHeckeDescent
