module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator.Five

@[expose] public section



/-! The degree-5 covariant-contraction anticommutator, mirroring
`covariant_contraction_anticommutator_two` (`TernaryPeriodPolynomials/DifferentialForm/Connection/Anticommutator.lean`)
exactly at k=5/4, using the two antisymmetrization formulas from `AnticommutatorFive.lean`. Unlike
k=2, the "contraction-of-exterior" term `symmetricContraction n 5 x (covariantExterior n 5 w x)` is
forced to `0` since it lives in the trivial module `FormValue n 6` (`SixVanishing.lean`); after
proving the full two-term identity (safe, mirrors a proven template exactly) we extract the
one-term corollary that is actually needed downstream. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory ContinuousAlternatingMap
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- The degree-5 covariant-contraction anticommutator (full two-term identity), mirroring
`covariant_contraction_anticommutator_two` exactly at k=5/4. -/
theorem covariant_contraction_anticommutator_five (n : ℕ) (w : Coordinates → FormValue n 5)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (hw : DifferentiableAt ℝ w x) :
    symmetricContraction n 5 x (covariantExterior n 5 w x) +
      covariantExterior n 4 (fun y => symmetricContraction n 4 y (w y)) x =
        symmetricDirectionalTrace n 5 w x := by
  apply ContinuousAlternatingMap.ext
  intro z
  have hz : z = ![z 0, z 1, z 2, z 3, z 4] := by ext i; fin_cases i <;> rfl
  rw [hz, ContinuousAlternatingMap.add_apply, covariantExterior_four_apply n _ x hx,
    covariantFormDerivative_symmetricContraction n 4 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 4 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 4 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 4 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 4 w x hx _ hw]
  simp only [symmetricContraction_apply, covariantExterior_five_apply n w x hx,
    symmetricDirectionalTrace, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  change
    (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 5 w x (Pi.single j 1) ![z 0, z 1, z 2, z 3, z 4] -
        covariantFormDerivative n 5 w x (z 0) ![Pi.single j 1, z 1, z 2, z 3, z 4] +
        covariantFormDerivative n 5 w x (z 1) ![Pi.single j 1, z 0, z 2, z 3, z 4] -
        covariantFormDerivative n 5 w x (z 2) ![Pi.single j 1, z 0, z 1, z 3, z 4] +
        covariantFormDerivative n 5 w x (z 3) ![Pi.single j 1, z 0, z 1, z 2, z 4] -
        covariantFormDerivative n 5 w x (z 4) ![Pi.single j 1, z 0, z 1, z 2, z 3])) +
    ((∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 5 w x (z 0) ![Pi.single j 1, z 1, z 2, z 3, z 4])) -
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 5 w x (z 1) ![Pi.single j 1, z 0, z 2, z 3, z 4])) +
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 5 w x (z 2) ![Pi.single j 1, z 0, z 1, z 3, z 4])) -
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 5 w x (z 3) ![Pi.single j 1, z 0, z 1, z 2, z 4])) +
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 5 w x (z 4) ![Pi.single j 1, z 0, z 1, z 2, z 3]))) =
    ∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 5 w x (Pi.single j 1) ![z 0, z 1, z 2, z 3, z 4])
  simp only [map_add, map_sub, _root_.smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

/-- One-term corollary: since `symmetricContraction n 5 x (covariantExterior n 5 w x) = 0` (its
argument lives in the trivial module `FormValue n 6`, `SixVanishing.lean`), the degree-5 covariant
exterior derivative of the degree-4 contraction equals the directional trace directly. This is
the identity actually needed downstream, mirroring how `weightedDivergence_energyCurrent_two` uses
`covariant_contraction_anticommutator_two`. -/
theorem covariant_contraction_anticommutator_five_contraction (n : ℕ)
    (w : Coordinates → FormValue n 5) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (hw : DifferentiableAt ℝ w x) :
    covariantExterior n 4 (fun y => symmetricContraction n 4 y (w y)) x =
      symmetricDirectionalTrace n 5 w x := by
  have h6 : covariantExterior n 5 w x = 0 := formValue_six_eq_zero n _
  have hA0 : symmetricContraction n 5 x (covariantExterior n 5 w x) = 0 := by
    rw [h6]
    apply ContinuousAlternatingMap.ext
    intro v
    simp [symmetricContraction_apply]
  have h := covariant_contraction_anticommutator_five n w x hx hw
  rwa [hA0, zero_add] at h

end TernaryPeriodPolynomials.Argument.Coercivity
