module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ZeroExterior
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Anticommutator
public import TernaryPeriodPolynomials.DifferentialForm.Connection.ContractionTensor

@[expose] public section



/-! # Degree-one contraction/covariant-derivative anticommutator identity

Mirrors `TernaryPoly.PolynomialFormConnection.covariant_contraction_anticommutator_two`
(`TernaryPeriodPolynomials/DifferentialForm/Connection/Anticommutator.lean`) one exterior degree down, using
the existing degree-0 base case `covariant_contraction_anticommutator_zero`
(`TernaryPeriodPolynomials.Argument.Coercivity.Anticommutator`, read-only reference,
imported transitively via `ZeroExterior`) as the structural template for the *simpler* side
(`covariantExterior n 0`), and `covariantExterior_one_apply`/`covariantFormDerivative_symmetricContraction`
(both already generic in the exterior degree) for the rest.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.CoercivityOne

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open ContinuousAlternatingMap
open TernaryPeriodPolynomials.Argument.Coercivity (covariantExterior_zero_apply)

/-- Degree-one anticommutator: contracting the covariant exterior derivative of a degree-one
form, plus the covariant exterior derivative of its own contraction, equals the symmetric
directional trace. The exterior-degree-one analogue of `covariant_contraction_anticommutator_two`
(two terms, unlike the degree-zero base case which has only one). -/
theorem covariant_contraction_anticommutator_one (n : ℕ) (w : Coordinates → FormValue n 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (hw : DifferentiableAt ℝ w x) :
    symmetricContraction n 1 x (covariantExterior n 1 w x) +
      covariantExterior n 0 (fun y => symmetricContraction n 0 y (w y)) x =
        symmetricDirectionalTrace n 1 w x := by
  apply ContinuousAlternatingMap.ext
  intro z
  have hz : z = ![z 0] := by ext i; fin_cases i; rfl
  rw [hz, ContinuousAlternatingMap.add_apply, covariantExterior_zero_apply n _ x hx,
    covariantFormDerivative_symmetricContraction n 0 w x hx _ hw]
  simp only [symmetricContraction_apply, covariantExterior_one_apply n w x hx,
    symmetricDirectionalTrace, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  change (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 1 w x (Pi.single j 1) ![z 0] -
        covariantFormDerivative n 1 w x (z 0) ![Pi.single j 1])) +
    (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 1 w x (z 0) ![Pi.single j 1])) =
    ∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 1 w x (Pi.single j 1) ![z 0])
  simp only [map_sub, smul_sub, Finset.sum_sub_distrib]
  abel

end TernaryPeriodPolynomials.Argument.CoercivityOne
