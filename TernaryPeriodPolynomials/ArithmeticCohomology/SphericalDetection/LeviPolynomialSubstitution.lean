module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PlaneRadicalCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LowerRadicalCoordinate

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem pderiv_linearForm (matrix : Matrix (Fin 3) (Fin 3) ℂ) (row coordinate : Fin 3) :
    pderiv coordinate (linearForm matrix row) = C (matrix row coordinate) := by
  fin_cases coordinate <;> simp [linearForm, Fin.sum_univ_three, pderiv_X]

theorem pderiv_substitute (matrix : Matrix (Fin 3) (Fin 3) ℂ) (coordinate : Fin 3)
    (polynomial : Poly) :
    pderiv coordinate (substitute matrix polynomial) =
      ∑ index, C (matrix index coordinate) * substitute matrix (pderiv index polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [substitute]
  | add first second first_eq second_eq =>
    simp only [map_add, first_eq, second_eq, mul_add, Finset.sum_add_distrib]
  | mul_X polynomial generator equality =>
    rw [map_mul, pderiv_mul, substitute_X, pderiv_linearForm, equality]
    fin_cases generator <;>
      simp [Fin.sum_univ_three, pderiv_X, substitute_X] <;> ring

theorem binaryPolynomialLift_pderiv (coordinate : Fin 2) (polynomial : Binary.Poly) :
    pderiv coordinate.castSucc (binaryPolynomialLift polynomial) =
      binaryPolynomialLift (pderiv coordinate polynomial) := by
  exact pderiv_rename (Fin.castSucc_injective 2) coordinate polynomial

theorem planeBlock_linearForm_binary (matrix : Matrix (Fin 2) (Fin 2) ℂ)
    (scalar : ℂ) (coordinate : Fin 2) :
    linearForm (planeBlock matrix scalar) coordinate.castSucc =
      binaryPolynomialLift (Binary.linearForm matrix coordinate) := by
  fin_cases coordinate <;>
    simp [linearForm, Binary.linearForm, planeBlock, binaryPolynomialLift,
      Fin.sum_univ_three, Fin.sum_univ_two]

theorem planeBlock_linearForm_third (matrix : Matrix (Fin 2) (Fin 2) ℂ) (scalar : ℂ) :
    linearForm (planeBlock matrix scalar) 2 = C scalar * X 2 := by
  simp [linearForm, planeBlock, Fin.sum_univ_three]

theorem substitute_planeBlock_lift (matrix : Matrix (Fin 2) (Fin 2) ℂ)
    (scalar : ℂ) (polynomial : Binary.Poly) :
    substitute (planeBlock matrix scalar) (binaryPolynomialLift polynomial) =
      binaryPolynomialLift (Binary.substitute matrix polynomial) := by
  have equality : (substitute (planeBlock matrix scalar)).comp binaryPolynomialLift =
      binaryPolynomialLift.comp (Binary.substitute matrix) := by
    apply MvPolynomial.algHom_ext
    intro coordinate
    simp only [AlgHom.comp_apply, binaryPolynomialLift, rename_X,
      substitute_X, Binary.substitute_X]
    exact planeBlock_linearForm_binary matrix scalar coordinate
  exact congrArg (fun hom : Binary.Poly →ₐ[ℂ] Poly => hom polynomial) equality

theorem restrict_substitute_planeBlock (matrix : Matrix (Fin 2) (Fin 2) ℂ)
    (scalar : ℂ) (polynomial : Poly) :
    binaryPolynomialRestrict (substitute (planeBlock matrix scalar) polynomial) =
      Binary.substitute matrix (binaryPolynomialRestrict polynomial) := by
  have equality : binaryPolynomialRestrict.comp (substitute (planeBlock matrix scalar)) =
      (Binary.substitute matrix).comp binaryPolynomialRestrict := by
    apply MvPolynomial.algHom_ext
    intro coordinate
    fin_cases coordinate <;>
      simp [AlgHom.comp_apply, substitute_X, linearForm, planeBlock,
        binaryPolynomialRestrict, Binary.substitute_X, Binary.linearForm,
        Fin.sum_univ_three, Fin.sum_univ_two]
  exact congrArg (fun hom : Poly →ₐ[ℂ] Binary.Poly => hom polynomial) equality

theorem pderiv_substitute_planeBlock_binary (matrix : Matrix (Fin 2) (Fin 2) ℂ)
    (scalar : ℂ) (coordinate : Fin 2) (polynomial : Poly) :
    pderiv coordinate.castSucc (substitute (planeBlock matrix scalar) polynomial) =
      ∑ index : Fin 2, C (matrix index coordinate) *
        substitute (planeBlock matrix scalar) (pderiv index.castSucc polynomial) := by
  rw [pderiv_substitute]
  fin_cases coordinate <;> simp [planeBlock, Fin.sum_univ_three, Fin.sum_univ_two]

theorem pderiv_substitute_planeBlock_third (matrix : Matrix (Fin 2) (Fin 2) ℂ)
    (scalar : ℂ) (polynomial : Poly) :
    pderiv 2 (substitute (planeBlock matrix scalar) polynomial) =
      C scalar * substitute (planeBlock matrix scalar) (pderiv 2 polynomial) := by
  rw [pderiv_substitute]
  simp [planeBlock, Fin.sum_univ_three]

theorem planeBlock_det (matrix : Matrix (Fin 2) (Fin 2) ℂ) (scalar : ℂ) :
    (planeBlock matrix scalar).det = matrix.det * scalar := by
  simp only [planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  simp
  ring

theorem planeLevi_det (matrix : Binary.GL2) (scalar : ℂˣ) :
    (GeneralLinearGroup.det (planeLevi matrix scalar)).val =
      (GeneralLinearGroup.det matrix).val * scalar.val := by
  exact planeBlock_det matrix.val scalar.val

theorem planeLevi_inverse (matrix : Binary.GL2) (scalar : ℂˣ) :
    (planeLevi matrix scalar)⁻¹ = planeLevi matrix⁻¹ scalar⁻¹ := by
  apply Units.ext
  rfl

theorem planeLevi_value (matrix : Binary.GL2) (scalar : ℂˣ) :
    (planeLevi matrix scalar).val = planeBlock matrix.val scalar.val := rfl

theorem planeLevi_determinantCharacter (exponent : ℤ) (matrix : Binary.GL2) (scalar : ℂˣ) :
    determinantCharacter exponent (planeLevi matrix scalar) =
      Binary.determinantCharacter exponent matrix * scalar.val ^ exponent := by
  change ((GeneralLinearGroup.det (planeLevi matrix scalar)).val) ^ exponent = _
  rw [planeLevi_det, mul_zpow]
  rfl

theorem action_planeLevi_lift (exponent : ℤ) (matrix : Binary.GL2) (scalar : ℂˣ)
    (polynomial : Binary.Poly) :
    action exponent (planeLevi matrix scalar) (binaryPolynomialLift polynomial) =
      scalar.val ^ exponent • binaryPolynomialLift (Binary.action exponent matrix polynomial) := by
  rw [action_apply, planeLevi_determinantCharacter, planeLevi_inverse]
  change (Binary.determinantCharacter exponent matrix * scalar.val ^ exponent) •
    substitute (planeBlock matrix⁻¹.val scalar⁻¹.val) (binaryPolynomialLift polynomial) = _
  rw [substitute_planeBlock_lift, Binary.action_apply, map_smul, smul_smul, mul_comm]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
