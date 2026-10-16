module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.ContractionTensor
public import TernaryPeriodPolynomials.DifferentialForm.Connection.ExteriorDegrees

@[expose] public section


/-! The genuine degree-two covariant-contraction anticommutator. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

/-- Actual contraction of the symmetric one-form with the covariant derivative. -/
def symmetricDirectionalTrace (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) : FormValue n k :=
  ∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j •
    coefficientFormMap (symmetricPart n x (Pi.single i 1)) k
      (covariantFormDerivative n k w x (Pi.single j 1))

theorem covariant_contraction_anticommutator_two (n : ℕ) (w : Coordinates → FormValue n 2)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (hw : DifferentiableAt ℝ w x) :
    symmetricContraction n 2 x (covariantExterior n 2 w x) +
      covariantExterior n 1 (fun y => symmetricContraction n 1 y (w y)) x =
        symmetricDirectionalTrace n 2 w x := by
  apply ContinuousAlternatingMap.ext
  intro z
  have hz : z = ![z 0, z 1] := by ext i; fin_cases i <;> rfl
  rw [hz, ContinuousAlternatingMap.add_apply, covariantExterior_one_apply n _ x hx,
    covariantFormDerivative_symmetricContraction n 1 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 1 w x hx _ hw]
  simp only [symmetricContraction_apply, covariantExterior_two_apply n w x hx,
    symmetricDirectionalTrace, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  change (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 2 w x (Pi.single j 1) ![z 0, z 1] -
        covariantFormDerivative n 2 w x (z 0) ![Pi.single j 1, z 1] +
        covariantFormDerivative n 2 w x (z 1) ![Pi.single j 1, z 0])) +
    ((∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 2 w x (z 0) ![Pi.single j 1, z 1])) -
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 2 w x (z 1) ![Pi.single j 1, z 0]))) =
    ∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 2 w x (Pi.single j 1) ![z 0, z 1])
  simp only [map_add, map_sub, _root_.smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end TernaryPoly.PolynomialFormConnection
