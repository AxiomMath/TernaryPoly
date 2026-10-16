module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ZeroExterior

@[expose] public section



/-! Degree-0 specialization of the contraction/covariant-derivative anticommutator identity.
At `k = 0` there is no second (contraction-of-derivative) term since `symmetricContraction n (-1)`
does not exist, so the identity is a direct equality, not a sum of two terms as at `k = 2`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open ContinuousAlternatingMap

/-- Degree-0 anticommutator: contracting the covariant exterior derivative of a degree-0 form
equals the symmetric directional trace of that form, with no extra cross term. -/
theorem covariant_contraction_anticommutator_zero (n : ℕ) (w : Coordinates → FormValue n 0)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    symmetricContraction n 0 x (covariantExterior n 0 w x) = symmetricDirectionalTrace n 0 w x := by
  apply ContinuousAlternatingMap.ext
  intro z
  have hz : z = (![] : Fin 0 → Coordinates) := by funext i; exact i.elim0
  subst hz
  simp only [symmetricContraction_apply, covariantExterior_zero_apply n w x hx,
    symmetricDirectionalTrace, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  rfl

end TernaryPeriodPolynomials.Argument.Coercivity
