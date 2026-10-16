module

public import TernaryPeriodPolynomials.Building.PlaneFlatExtensions
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization

@[expose] public section


/-! Compose the three accepted analytic results using the composition of the accepted statements, avoiding a second copy of their proof libraries. -/

namespace TernaryPeriodPolynomials.EisensteinHolomorphy
open GeneralEisenstein

theorem eisenstein_holomorphy (n : ℕ) (hn : 0 < n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) : PlaneEisensteinHolomorphic D :=
  eisenstein_holomorphy_of_pieces
    { flat := PlaneFlatExtensions.plane_flat_extensions
      continuation := PlaneEisensteinContinuation.plane_eisenstein_continuation
      regularization := EisensteinRegularization.eisenstein_regularization }
    n hn D hχ

end TernaryPeriodPolynomials.EisensteinHolomorphy
