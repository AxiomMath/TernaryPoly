module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator.Three
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator.Five

@[expose] public section



/-! Degree-4 (`k = 3`-shaped, output degree 4→5 and contraction 5→4) covariant-contraction
anticommutator, mirroring `covariant_contraction_anticommutator_three` (`AnticommutatorThree.lean`)
one level up. Both `FormValue n 3` and `FormValue n 5` are nontrivial, so (as at degree 3) the full
two-term identity is what is needed downstream. Both antisymmetrization formulas this needs already
exist: the lower-term unfolding reuses `covariantExterior_three_apply` (`AnticommutatorThree.lean`),
and the upper-term unfolding reuses `covariantExterior_four_apply`, which was already built in
`AnticommutatorFive.lean` for an unrelated purpose (degree 5's own one-term anticommutator identity)
but is exactly the same fact needed here, since both concern `covariantExterior n 4`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory ContinuousAlternatingMap
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The degree-4 covariant-contraction anticommutator, mirroring
`covariant_contraction_anticommutator_three` one level up. -/
theorem covariant_contraction_anticommutator_four (n : ℕ) (w : Coordinates → FormValue n 4)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (hw : DifferentiableAt ℝ w x) :
    symmetricContraction n 4 x (covariantExterior n 4 w x) +
      covariantExterior n 3 (fun y => symmetricContraction n 3 y (w y)) x =
        symmetricDirectionalTrace n 4 w x := by
  apply ContinuousAlternatingMap.ext
  intro z
  have hz : z = ![z 0, z 1, z 2, z 3] := by ext i; fin_cases i <;> rfl
  rw [hz, ContinuousAlternatingMap.add_apply, covariantExterior_three_apply n _ x hx,
    covariantFormDerivative_symmetricContraction n 3 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 3 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 3 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 3 w x hx _ hw]
  simp only [symmetricContraction_apply, covariantExterior_four_apply n w x hx,
    symmetricDirectionalTrace, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  change
    (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 4 w x (Pi.single j 1) ![z 0, z 1, z 2, z 3] -
        covariantFormDerivative n 4 w x (z 0) ![Pi.single j 1, z 1, z 2, z 3] +
        covariantFormDerivative n 4 w x (z 1) ![Pi.single j 1, z 0, z 2, z 3] -
        covariantFormDerivative n 4 w x (z 2) ![Pi.single j 1, z 0, z 1, z 3] +
        covariantFormDerivative n 4 w x (z 3) ![Pi.single j 1, z 0, z 1, z 2])) +
    ((∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 4 w x (z 0) ![Pi.single j 1, z 1, z 2, z 3])) -
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 4 w x (z 1) ![Pi.single j 1, z 0, z 2, z 3])) +
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 4 w x (z 2) ![Pi.single j 1, z 0, z 1, z 3])) -
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 4 w x (z 3) ![Pi.single j 1, z 0, z 1, z 2]))) =
    ∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 4 w x (Pi.single j 1) ![z 0, z 1, z 2, z 3])
  simp only [map_add, map_sub, _root_.smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end TernaryPeriodPolynomials.Argument.Coercivity
