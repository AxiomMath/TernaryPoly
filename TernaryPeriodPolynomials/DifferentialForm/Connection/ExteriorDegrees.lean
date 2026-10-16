module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.ExteriorTensor

@[expose] public section

/-! Explicit genuine tensor alternation in the two degrees needed for mixed energy. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SmoothCoveringDeRham ContinuousAlternatingMap
open scoped Matrix.Norms.Elementwise

theorem covariantExterior_one_apply (n : ℕ) (w : Coordinates → FormValue n 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    covariantExterior n 1 w x ![u, v] =
      covariantFormDerivative n 1 w x u ![v] - covariantFormDerivative n 1 w x v ![u] := by
  rw [← alternatize_covariantFormLinearDerivative n 1 w x hx]
  have h : Fin.removeNth (1 : Fin 2) ![u, v] = ![u] := by
    ext j; fin_cases j; rfl
  simp [alternatizeUncurryFin_apply, Fin.sum_univ_two, h, sub_eq_add_neg,
    covariantFormLinearDerivative_apply]

theorem covariantExterior_two_apply (n : ℕ) (w : Coordinates → FormValue n 2)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v z : Coordinates) :
    covariantExterior n 2 w x ![u, v, z] =
      covariantFormDerivative n 2 w x u ![v, z] - covariantFormDerivative n 2 w x v ![u, z] +
        covariantFormDerivative n 2 w x z ![u, v] := by
  rw [← alternatize_covariantFormLinearDerivative n 2 w x hx]
  have h1 : Fin.removeNth (1 : Fin 3) ![u, v, z] = ![u, z] := by
    ext j; fin_cases j <;> rfl
  have h2 : Fin.removeNth (2 : Fin 3) ![u, v, z] = ![u, v] := by
    ext j; fin_cases j <;> rfl
  simp [alternatizeUncurryFin_apply, Fin.sum_univ_succ, h1, h2, sub_eq_add_neg, add_assoc,
    covariantFormLinearDerivative_apply]

end TernaryPoly.PolynomialFormConnection
