module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ShearPolynomialCurve

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem homogeneousShearDerivation_smul_power_coe (degree : ℕ) (coordinate multiplier : Fin 3)
    (scalar : ℂ) (power : ℕ) (polynomial : HomogeneousPoly degree) :
    (((scalar • homogeneousShearDerivation degree coordinate multiplier) ^ power) polynomial).val =
      ((scalar • polynomialShearDerivation coordinate multiplier) ^ power) polynomial.val := by
  rw [smul_pow, smul_pow, LinearMap.smul_apply, Submodule.coe_smul, LinearMap.smul_apply,
    homogeneousShearDerivation_power_coe]

theorem homogeneousShearDerivation_smul_power_zero (degree : ℕ) (coordinate multiplier : Fin 3)
    (scalar : ℂ) (distinct : multiplier ≠ coordinate) :
    (scalar • homogeneousShearDerivation degree coordinate multiplier) ^ (degree + 1) = 0 := by
  rw [smul_pow, homogeneousShearDerivation_power_zero degree coordinate multiplier distinct, smul_zero]

theorem rationalEnd_smul_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (scalar : ℚ) (operator : Module.End ℂ V) (vector : V) :
    (scalar • operator) vector = (scalar : ℂ) • operator vector := rfl

theorem rationalHomogeneousEnd_smul_coe (degree : ℕ) (scalar : ℚ)
    (operator : Module.End ℂ (HomogeneousPoly degree)) (polynomial : HomogeneousPoly degree) :
    ((scalar • operator) polynomial).val = scalar • (operator polynomial).val := by
  rw [LinearMap.smul_apply, Submodule.coe_smul_of_tower]

theorem homogeneousShearDerivation_exponential_coe (degree : ℕ) (coordinate multiplier : Fin 3)
    (scalar : ℂ) (distinct : multiplier ≠ coordinate) (polynomial : HomogeneousPoly degree) :
    (IsNilpotent.exp (scalar • homogeneousShearDerivation degree coordinate multiplier) polynomial).val =
      Polynomial.eval 1 (shearPolynomialCurve coordinate multiplier scalar polynomial.val) := by
  rw [IsNilpotent.exp_eq_sum
    (homogeneousShearDerivation_smul_power_zero degree coordinate multiplier scalar distinct),
    shearPolynomialCurve_finite_taylor coordinate multiplier scalar distinct polynomial]
  simp only [LinearMap.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro power _
  rw [rationalHomogeneousEnd_smul_coe, homogeneousShearDerivation_smul_power_coe]

theorem shearPolynomialCurve_eval_one (coordinate multiplier : Fin 3) (scalar : ℂ) (polynomial : Poly) :
    Polynomial.eval 1 (shearPolynomialCurve coordinate multiplier scalar polynomial) =
      MvPolynomial.bind₁ (fun index => X index + if index = coordinate then C scalar * X multiplier else 0) polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C constant => simp
  | add first second first_eq second_eq => simp [first_eq, second_eq]
  | mul_X polynomial generator equality =>
    rw [map_mul, Polynomial.eval_mul, equality, map_mul, bind₁_X_right, shearPolynomialCurve_X]
    by_cases same : generator = coordinate <;> simp [same]

theorem upperRadicalGenerator_exponential (degree : ℕ) (coordinate : Fin 2) :
    IsNilpotent.exp (upperRadicalGenerator degree coordinate) =
      homogeneousAction degree (-1)
        (planeUnipotent (if coordinate = 0 then 1 else 0) (if coordinate = 1 then 1 else 0)) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [upperRadicalGenerator, homogeneousShearDerivation_exponential_coe degree coordinate.castSucc 2 (-1)
    (Ne.symm (Fin.castSucc_ne_last coordinate)), shearPolynomialCurve_eval_one,
    homogeneousAction_coe, action_apply]
  have determinant : determinantCharacter (-1)
      (planeUnipotent (if coordinate = 0 then (1 : ℂ) else 0) (if coordinate = 1 then 1 else 0)) = 1 := by
    change ((planeUnipotent (if coordinate = 0 then (1 : ℂ) else 0)
      (if coordinate = 1 then 1 else 0)).val.det) ^ (-1 : ℤ) = 1
    fin_cases coordinate <;> simp [planeUnipotent, Matrix.det_fin_three]
  rw [determinant, one_smul]
  have substitutions : MvPolynomial.bind₁
      (fun index => X index + if index = coordinate.castSucc then C (-1 : ℂ) * X 2 else 0) =
      substitute (planeUnipotent (if coordinate = 0 then (1 : ℂ) else 0)
        (if coordinate = 1 then 1 else 0))⁻¹.val := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases coordinate <;> fin_cases index <;>
      simp [substitute_X, linearForm, planeUnipotent, Fin.sum_univ_three]
  rw [substitutions]

theorem lowerRadicalGenerator_exponential (degree : ℕ) (coordinate : Fin 2) :
    IsNilpotent.exp (lowerRadicalGenerator degree coordinate) =
      homogeneousAction degree (-1)
        (lowerPlaneUnipotent (if coordinate = 0 then 3 else 0) (if coordinate = 1 then 3 else 0)) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [lowerRadicalGenerator, homogeneousShearDerivation_exponential_coe degree 2 coordinate.castSucc (-3)
    (Fin.castSucc_ne_last coordinate), shearPolynomialCurve_eval_one,
    homogeneousAction_coe, action_apply]
  have determinant : determinantCharacter (-1)
      (lowerPlaneUnipotent (if coordinate = 0 then (3 : ℂ) else 0) (if coordinate = 1 then 3 else 0)) = 1 := by
    change ((lowerPlaneUnipotent (if coordinate = 0 then (3 : ℂ) else 0)
      (if coordinate = 1 then 3 else 0)).val.det) ^ (-1 : ℤ) = 1
    fin_cases coordinate <;> simp [lowerPlaneUnipotent, Matrix.det_fin_three]
  rw [determinant, one_smul]
  have substitutions : MvPolynomial.bind₁
      (fun index => X index + if index = (2 : Fin 3) then C (-3 : ℂ) * X coordinate.castSucc else 0) =
      substitute (lowerPlaneUnipotent (if coordinate = 0 then (3 : ℂ) else 0)
        (if coordinate = 1 then 3 else 0))⁻¹.val := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases coordinate <;> fin_cases index <;>
      simp [substitute_X, linearForm, lowerPlaneUnipotent, Fin.sum_univ_three, add_comm]
  rw [substitutions]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
