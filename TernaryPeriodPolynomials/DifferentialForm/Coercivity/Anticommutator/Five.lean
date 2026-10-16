module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Cancellation
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SixVanishing

@[expose] public section



/-! Degree-5 (`k = 4`) antisymmetrization formula for `covariantExterior`, mirroring
`covariantExterior_one_apply`/`covariantExterior_two_apply`
(`TernaryPeriodPolynomials/DifferentialForm/Connection/ExteriorDegrees.lean`) at five arguments. This is
preparatory for a degree-5 anticommutator identity: unlike the k=1,2 cases, degree 5 only
ever needs this with the *contraction* `S₄ ∘ w` substituted for `w`, since the companion
`covariantExterior n 5 w x`-side term of the general two-term anticommutator is forced to
`0` by `SixVanishing.lean` (`FormValue n 6` is trivial). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory ContinuousAlternatingMap
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- `covariantExterior` at degree 4 (five arguments), mirroring `covariantExterior_two_apply`. -/
theorem covariantExterior_four_apply (n : ℕ) (w : Coordinates → FormValue n 4)
    (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u0 u1 u2 u3 u4 : Coordinates) :
    covariantExterior n 4 w x ![u0, u1, u2, u3, u4] =
      covariantFormDerivative n 4 w x u0 ![u1, u2, u3, u4] -
        covariantFormDerivative n 4 w x u1 ![u0, u2, u3, u4] +
        covariantFormDerivative n 4 w x u2 ![u0, u1, u3, u4] -
        covariantFormDerivative n 4 w x u3 ![u0, u1, u2, u4] +
        covariantFormDerivative n 4 w x u4 ![u0, u1, u2, u3] := by
  rw [← alternatize_covariantFormLinearDerivative n 4 w x hx]
  have h0 : Fin.removeNth (0 : Fin 5) ![u0, u1, u2, u3, u4] = ![u1, u2, u3, u4] := by
    ext j; fin_cases j <;> rfl
  have h1 : Fin.removeNth (1 : Fin 5) ![u0, u1, u2, u3, u4] = ![u0, u2, u3, u4] := by
    ext j; fin_cases j <;> rfl
  have h2 : Fin.removeNth (2 : Fin 5) ![u0, u1, u2, u3, u4] = ![u0, u1, u3, u4] := by
    ext j; fin_cases j <;> rfl
  have h3 : Fin.removeNth (3 : Fin 5) ![u0, u1, u2, u3, u4] = ![u0, u1, u2, u4] := by
    ext j; fin_cases j <;> rfl
  have h4 : Fin.removeNth (4 : Fin 5) ![u0, u1, u2, u3, u4] = ![u0, u1, u2, u3] := by
    ext j; fin_cases j <;> rfl
  simp [alternatizeUncurryFin_apply, Fin.sum_univ_five, h0, h1, h2, h3, h4, sub_eq_add_neg,
    add_assoc, covariantFormLinearDerivative_apply]

/-- `covariantExterior` at degree 5 (six arguments), mirroring `covariantExterior_four_apply`
one level up. Used only to extract, via `formValue_six_eq_zero`, the vanishing relation among
its six summands (`AnticommutatorFiveIdentity.lean`). -/
theorem covariantExterior_five_apply (n : ℕ) (w : Coordinates → FormValue n 5)
    (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u0 u1 u2 u3 u4 u5 : Coordinates) :
    covariantExterior n 5 w x ![u0, u1, u2, u3, u4, u5] =
      covariantFormDerivative n 5 w x u0 ![u1, u2, u3, u4, u5] -
        covariantFormDerivative n 5 w x u1 ![u0, u2, u3, u4, u5] +
        covariantFormDerivative n 5 w x u2 ![u0, u1, u3, u4, u5] -
        covariantFormDerivative n 5 w x u3 ![u0, u1, u2, u4, u5] +
        covariantFormDerivative n 5 w x u4 ![u0, u1, u2, u3, u5] -
        covariantFormDerivative n 5 w x u5 ![u0, u1, u2, u3, u4] := by
  rw [← alternatize_covariantFormLinearDerivative n 5 w x hx]
  have h0 : Fin.removeNth (0 : Fin 6) ![u0, u1, u2, u3, u4, u5] = ![u1, u2, u3, u4, u5] := by
    ext j; fin_cases j <;> rfl
  have h1 : Fin.removeNth (1 : Fin 6) ![u0, u1, u2, u3, u4, u5] = ![u0, u2, u3, u4, u5] := by
    ext j; fin_cases j <;> rfl
  have h2 : Fin.removeNth (2 : Fin 6) ![u0, u1, u2, u3, u4, u5] = ![u0, u1, u3, u4, u5] := by
    ext j; fin_cases j <;> rfl
  have h3 : Fin.removeNth (3 : Fin 6) ![u0, u1, u2, u3, u4, u5] = ![u0, u1, u2, u4, u5] := by
    ext j; fin_cases j <;> rfl
  have h4 : Fin.removeNth (4 : Fin 6) ![u0, u1, u2, u3, u4, u5] = ![u0, u1, u2, u3, u5] := by
    ext j; fin_cases j <;> rfl
  have h5 : Fin.removeNth (5 : Fin 6) ![u0, u1, u2, u3, u4, u5] = ![u0, u1, u2, u3, u4] := by
    ext j; fin_cases j <;> rfl
  simp [alternatizeUncurryFin_apply, Fin.sum_univ_six, h0, h1, h2, h3, h4, h5, sub_eq_add_neg,
    add_assoc, covariantFormLinearDerivative_apply]

end TernaryPeriodPolynomials.Argument.Coercivity
