module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Cancellation
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.CoefficientCasimir

@[expose] public section



/-! Degree-0 specializations of the generic (in `k`) exterior-derivative/basepoint machinery
used by the project's degree-2 coercivity argument, needed for Proposition C.1's degree-0 clause. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open ContinuousAlternatingMap

/-- `symmetricExterior` at degree 0: the single term, no sign, feeding the empty tuple to `a`. -/
theorem symmetricExterior_zero_apply (n : ℕ) (x : Coordinates) (a : FormValue n 0) (u : Coordinates) :
    symmetricExterior n 0 x a ![u] = symmetricPart n x u (a ![]) := by
  have h : Fin.removeNth (0 : Fin 1) ![u] = (![] : Fin 0 → Coordinates) := by
    ext j; exact j.elim0
  simp [symmetricExterior_apply, h]

/-- `covariantExterior` at degree 0. -/
theorem covariantExterior_zero_apply (n : ℕ) (w : Coordinates → FormValue n 0)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (u : Coordinates) :
    covariantExterior n 0 w x ![u] = covariantFormDerivative n 0 w x u ![] := by
  rw [← alternatize_covariantFormLinearDerivative n 0 w x hx]
  have h : Fin.removeNth (0 : Fin 1) ![u] = (![] : Fin 0 → Coordinates) := by
    ext j; exact j.elim0
  simp [alternatizeUncurryFin_apply, h, covariantFormLinearDerivative_apply]

/-- The symmetric exterior derivative at the basepoint, degree 0, in terms of `infinitesimal`. -/
theorem symmetricExterior_zero_basepoint (n : ℕ) (a : FormValue n 0) (i : Fin 5) :
    (symmetricExterior n 0 (coordinateChart basepoint) a ![baseFrame i]).val =
      (1 / 2 : ℝ) • infinitesimal (tangentFrame i) (a ![]).val := by
  rw [symmetricExterior_zero_apply, symmetricPart_baseFrame]
  simp only [_root_.smul_apply, infinitesimalCLM_apply, Submodule.coe_smul, coefficientInfinitesimal_apply]

/-- `formPairing` at degree 0 and the basepoint collapses to the bare coefficient pairing. -/
theorem formPairing_basepoint_zero (n : ℕ) (a b : FormValue n 0) :
    formPairing n 0 (coordinateChart basepoint) a b = factorialPairing (a ![]).val (b ![]).val := by
  have hv : ∀ I : Fin 0 → Fin 5, (fun r : Fin 0 => baseFrame (I r)) = (![] : Fin 0 → Coordinates) := by
    intro I; funext r; exact r.elim0
  rw [formPairing_basepoint_frame]
  simp [hv]

end TernaryPeriodPolynomials.Argument.Coercivity
