module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LineStabilizer

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {R S : Type} [CommRing R] [CommRing S]

theorem map_lineUnipotent (homomorphism : R →+* S) (first second : R) :
    GeneralLinearGroup.map homomorphism (lineUnipotent first second) =
      lineUnipotent (homomorphism first) (homomorphism second) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map_apply, lineUnipotent, upperUnipotent]

theorem lineUnipotent_inverse (first second : R) :
    (lineUnipotent first second)⁻¹ = lineUnipotent (-first) (-second) := by
  apply Units.ext
  rfl

theorem lineUnipotent_determinant (first second : R) :
    GeneralLinearGroup.det (lineUnipotent first second) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply]
  simp [lineUnipotent, upperUnipotent, Matrix.det_fin_three]

theorem lineUnipotent_substitute (first second : ℂ) :
    substitute (lineUnipotent first second).val =
      bind₁ ![X 0 + C first * X 1 + C second * X 2, X 1, X 2] := by
  change bind₁ (linearForm (lineUnipotent first second).val) = _
  apply congrArg (fun forms : Fin 3 → Poly => bind₁ forms)
  funext index
  fin_cases index <;>
    simp [linearForm, lineUnipotent, upperUnipotent, Fin.sum_univ_three]

theorem action_lineUnipotent (first second : ℂ) (polynomial : Poly) :
    action (-1) (lineUnipotent first second) polynomial =
      bind₁ ![X 0 - C first * X 1 - C second * X 2, X 1, X 2] polynomial := by
  rw [action_apply]
  have determinant : determinantCharacter (-1) (lineUnipotent first second) = 1 := by
    have matrixDeterminant : (lineUnipotent first second).val.det = 1 := by
      simpa only [GeneralLinearGroup.val_det_apply, Units.val_one] using
        congrArg Units.val (lineUnipotent_determinant first second)
    simp [determinantCharacter, matrixDeterminant]
  rw [determinant, one_smul, lineUnipotent_inverse, lineUnipotent_substitute]
  have forms :
      ( ![X 0 + C (-first) * X 1 + C (-second) * X 2, X 1, X 2] : Fin 3 → Poly) =
        ![X 0 - C first * X 1 - C second * X 2, X 1, X 2] := by
    funext index
    fin_cases index <;> simp [sub_eq_add_neg, add_assoc]
  exact congrArg (fun forms : Fin 3 → Poly => bind₁ forms polynomial) forms

theorem rationalCoefficientComponent_lineUnipotent (degree : ℕ)
    (first second : ℚ) (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter
        (lineUnipotent first second) polynomial).val =
      bind₁ ![X 0 - C (first : ℂ) * X 1 - C (second : ℂ) * X 2, X 1, X 2]
        polynomial.val := by
  have character : componentCharacter trivialCharacter
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lineUnipotent first second)) = 1 := by
    rfl
  change (componentCharacter trivialCharacter
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lineUnipotent first second)) •
    homogeneousAction degree (-1)
      (GeneralLinearGroup.map (algebraMap ℝ ℂ)
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lineUnipotent first second)))
        polynomial).val = _
  rw [character, one_smul, map_lineUnipotent, map_lineUnipotent]
  simpa using action_lineUnipotent
    (algebraMap ℝ ℂ (algebraMap ℚ ℝ first))
    (algebraMap ℝ ℂ (algebraMap ℚ ℝ second)) polynomial.val

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
