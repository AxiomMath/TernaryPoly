module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.TwoSideSelfAux0
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.TwoSideSelfAux1
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.TwoSideSelfAux2
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.TwoSideSelfAux3
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.TwoSideSelfAux4

@[expose] public section



/-! Helper for ISOMETRY: the two-sided (`TwoCoordinates`) half of the Hodge-star involution,
`star3to2 (star2to3 a) = (1/96) • a` for alternating `a`. Not one of the seven named identities,
but needed to reduce ISOMETRY to `twoPairing` via the adjoint lemmas in `HodgeStarAdjoint.lean`:
plugging `star2to3 b` into `star3to2_star2to3_adjoint` leaves a `star3to2 (star2to3 a)` term that
only this fact can resolve back to a bare `a`. Unlike R1-R4, neither `star2to3` nor `star3to2`
touches `infinitesimal`/`tangentFrame`, so each slice is a plain numeral brute force (no
`Derivation` unfolding); it is assembled from the five first-index slices
`star3to2_star2to3_self_aux0`..`star3to2_star2to3_self_aux4`, each independently checked. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star3to2_star2to3_self (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    star3to2 (star2to3 a) = (1/96 : ℝ) • a := by
  funext i j
  fin_cases i
  · exact star3to2_star2to3_self_aux0 a ha j
  · exact star3to2_star2to3_self_aux1 a ha j
  · exact star3to2_star2to3_self_aux2 a ha j
  · exact star3to2_star2to3_self_aux3 a ha j
  · exact star3to2_star2to3_self_aux4 a ha j

end TernaryPeriodPolynomials.Argument.Coercivity
