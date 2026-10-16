module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.PlusRep

@[expose] public section


/-!
# The pivot intertwiner on polynomials (LS14b)

`toPoly_pivotT : (pivotT n q : Poly) = -(bind₁ ![X 2, X 1, X 0] q)` (the permutation `X ↔ Z` with the determinant sign `det Π = -1`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein MvPolynomial Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem pivotR_val (i j : Fin 3) :
    (pivotR : GL (Fin 3) ℝ).val i j = if i.rev = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [pivotR, rationalGoodLine, GeneralLinearGroup.map_apply, Fin.rev]

theorem toPoly_pivotT (n : ℕ) (q : HomogeneousPoly n) :
    ((pivotT n q : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      -(bind₁ (![X 2, X 1, X 0] : Fin 3 → MvPolynomial (Fin 3) ℂ) (q : MvPolynomial (Fin 3) ℂ)) := by
  change ((GeneralEisenstein.action (-1) (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) pivotR))
    (q : MvPolynomial (Fin 3) ℂ)) = _
  rw [GeneralEisenstein.action_apply]
  have hinv : (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) pivotR)⁻¹ =
      Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) pivotR := by
    rw [inv_eq_iff_mul_eq_one, ← map_mul, pivotR_mul_self, map_one]
  rw [hinv]
  have hdet : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) pivotR) : ℂˣ) : ℂ) = -1 := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, pivotR, rationalGoodLine,
      Matrix.det_fin_three]
  have hlf : GeneralEisenstein.linearForm
      ((Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) pivotR : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      (![X 2, X 1, X 0] : Fin 3 → MvPolynomial (Fin 3) ℂ) := by
    funext i
    fin_cases i <;>
      simp [GeneralEisenstein.linearForm, Fin.sum_univ_three, Matrix.GeneralLinearGroup.map_apply, pivotR,
        rationalGoodLine]
  have hs : GeneralEisenstein.substitute
      ((Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) pivotR : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      bind₁ (![X 2, X 1, X 0] : Fin 3 → MvPolynomial (Fin 3) ℂ) := by
    unfold GeneralEisenstein.substitute
    rw [hlf]
  change (((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) pivotR) : ℂˣ) : ℂ) ^ (-1 : ℤ)) •
    GeneralEisenstein.substitute _ _ = _
  rw [hs, hdet]
  simp

end TernaryPeriodPolynomials.Argument.LineSeed
