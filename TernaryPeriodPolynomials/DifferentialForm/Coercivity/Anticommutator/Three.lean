module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Anticommutator

@[expose] public section



/-! Degree-3 (`k = 2`-shaped, output degree 3→4 and contraction 4→3) antisymmetrization formula for
`covariantExterior` and the degree-3 covariant-contraction anticommutator, mirroring
`covariantExterior_two_apply`/`covariant_contraction_anticommutator_two`
(`TernaryPeriodPolynomials/DifferentialForm/Connection/ExteriorDegrees.lean`/`...Anticommutator.lean`) one level up.
Unlike the degree-4/5 case (`AnticommutatorFive.lean`/`AnticommutatorFiveIdentity.lean`), neither
term vanishes here: both `FormValue n 2` and `FormValue n 4` are nontrivial, so the full two-term
identity is exactly what is needed downstream (no one-term corollary). The second LHS term's own
unfolding reuses the already-existing `covariantExterior_two_apply` directly; only the first LHS
term's unfolding (`covariantExterior_three_apply`) is new. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory ContinuousAlternatingMap
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- `covariantExterior` at degree 3 (four arguments), mirroring `covariantExterior_two_apply`. -/
theorem covariantExterior_three_apply (n : ℕ) (w : Coordinates → FormValue n 3)
    (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u0 u1 u2 u3 : Coordinates) :
    covariantExterior n 3 w x ![u0, u1, u2, u3] =
      covariantFormDerivative n 3 w x u0 ![u1, u2, u3] -
        covariantFormDerivative n 3 w x u1 ![u0, u2, u3] +
        covariantFormDerivative n 3 w x u2 ![u0, u1, u3] -
        covariantFormDerivative n 3 w x u3 ![u0, u1, u2] := by
  rw [← alternatize_covariantFormLinearDerivative n 3 w x hx]
  have h0 : Fin.removeNth (0 : Fin 4) ![u0, u1, u2, u3] = ![u1, u2, u3] := by
    ext j; fin_cases j <;> rfl
  have h1 : Fin.removeNth (1 : Fin 4) ![u0, u1, u2, u3] = ![u0, u2, u3] := by
    ext j; fin_cases j <;> rfl
  have h2 : Fin.removeNth (2 : Fin 4) ![u0, u1, u2, u3] = ![u0, u1, u3] := by
    ext j; fin_cases j <;> rfl
  have h3 : Fin.removeNth (3 : Fin 4) ![u0, u1, u2, u3] = ![u0, u1, u2] := by
    ext j; fin_cases j <;> rfl
  simp [alternatizeUncurryFin_apply, Fin.sum_univ_four, h0, h1, h2, h3, sub_eq_add_neg,
    add_assoc, covariantFormLinearDerivative_apply]

/-- The degree-3 covariant-contraction anticommutator, mirroring
`covariant_contraction_anticommutator_two` one level up. -/
theorem covariant_contraction_anticommutator_three (n : ℕ) (w : Coordinates → FormValue n 3)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (hw : DifferentiableAt ℝ w x) :
    symmetricContraction n 3 x (covariantExterior n 3 w x) +
      covariantExterior n 2 (fun y => symmetricContraction n 2 y (w y)) x =
        symmetricDirectionalTrace n 3 w x := by
  apply ContinuousAlternatingMap.ext
  intro z
  have hz : z = ![z 0, z 1, z 2] := by ext i; fin_cases i <;> rfl
  rw [hz, ContinuousAlternatingMap.add_apply, covariantExterior_two_apply n _ x hx,
    covariantFormDerivative_symmetricContraction n 2 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 2 w x hx _ hw,
    covariantFormDerivative_symmetricContraction n 2 w x hx _ hw]
  simp only [symmetricContraction_apply, covariantExterior_three_apply n w x hx,
    symmetricDirectionalTrace, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  change
    (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 3 w x (Pi.single j 1) ![z 0, z 1, z 2] -
        covariantFormDerivative n 3 w x (z 0) ![Pi.single j 1, z 1, z 2] +
        covariantFormDerivative n 3 w x (z 1) ![Pi.single j 1, z 0, z 2] -
        covariantFormDerivative n 3 w x (z 2) ![Pi.single j 1, z 0, z 1])) +
    ((∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 3 w x (z 0) ![Pi.single j 1, z 1, z 2])) -
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 3 w x (z 1) ![Pi.single j 1, z 0, z 2])) +
     (∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 3 w x (z 2) ![Pi.single j 1, z 0, z 1]))) =
    ∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j • symmetricPart n x (Pi.single i 1)
      (covariantFormDerivative n 3 w x (Pi.single j 1) ![z 0, z 1, z 2])
  simp only [map_add, map_sub, _root_.smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end TernaryPeriodPolynomials.Argument.Coercivity
