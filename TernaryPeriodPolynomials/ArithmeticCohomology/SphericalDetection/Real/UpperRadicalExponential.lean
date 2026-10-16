module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalCocycleDetection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneCuspidalAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem upperRadicalGenerator_exponential_parameter (degree : ℕ) (coordinate : Fin 2) (parameter : ℂ) :
    IsNilpotent.exp (parameter • upperRadicalGenerator degree coordinate) =
      homogeneousAction degree (-1)
        (planeUnipotent (if coordinate = 0 then parameter else 0) (if coordinate = 1 then parameter else 0)) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [upperRadicalGenerator, smul_smul, mul_neg_one,
    homogeneousShearDerivation_exponential_coe degree coordinate.castSucc 2 (-parameter)
      (Ne.symm (Fin.castSucc_ne_last coordinate)), shearPolynomialCurve_eval_one,
    homogeneousAction_coe, action_apply]
  have determinant : determinantCharacter (-1)
      (planeUnipotent (if coordinate = 0 then parameter else 0) (if coordinate = 1 then parameter else 0)) = 1 := by
    change ((planeUnipotent (if coordinate = 0 then parameter else 0)
      (if coordinate = 1 then parameter else 0)).val.det) ^ (-1 : ℤ) = 1
    fin_cases coordinate <;> simp [planeUnipotent, Matrix.det_fin_three]
  rw [determinant, one_smul]
  have substitutions : MvPolynomial.bind₁
      (fun index => X index + if index = coordinate.castSucc then C (-parameter) * X 2 else 0) =
      substitute (planeUnipotent (if coordinate = 0 then parameter else 0)
        (if coordinate = 1 then parameter else 0))⁻¹.val := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases coordinate <;> fin_cases index <;>
      simp [substitute_X, linearForm, planeUnipotent, Fin.sum_univ_three]
  rw [substitutions]

abbrev realUpperRadicalRep (degree : ℕ) : Rep ℂ RealPlaneRadical :=
  Rep.of ((realCoefficientComponent degree trivialCharacter).comp realPlaneRadicalMatrix)

theorem realUpperRadicalRep_axis (degree : ℕ) (coordinate : Fin 2) (parameter : ℝ) :
    (realUpperRadicalRep degree).ρ (realRadicalAxis coordinate parameter) =
      IsNilpotent.exp ((parameter : ℂ) • upperRadicalGenerator degree coordinate) := by
  rw [upperRadicalGenerator_exponential_parameter]
  apply LinearMap.ext
  intro polynomial
  change HomogeneousPoly degree at polynomial
  change realCoefficientComponent degree trivialCharacter
    (realPlaneRadicalMatrix (realRadicalAxis coordinate parameter)) polynomial = _
  rw [realCoefficientComponent_trivial]
  change homogeneousAction degree (-1)
    (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (planeUnipotent ((realRadicalAxis coordinate parameter).toAdd 0) ((realRadicalAxis coordinate parameter).toAdd 1))) polynomial = _
  rw [map_planeUnipotent]
  fin_cases coordinate <;> simp [realRadicalAxis]

theorem realUpperRadicalRep_lattice (degree : ℕ) (element : RadicalLattice) :
    (realUpperRadicalRep degree).ρ (radicalLatticeReal element) = (upperRadicalLatticeRep degree).ρ element := by
  apply LinearMap.ext
  intro polynomial
  change realCoefficientComponent degree trivialCharacter
    (planeUnipotent (element.toAdd.1 : ℝ) (element.toAdd.2 : ℝ)) polynomial =
      realCoefficientComponent degree trivialCharacter
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (planeUnipotent (element.toAdd.1 : ℚ) (element.toAdd.2 : ℚ))) polynomial
  rw [map_planeUnipotent]
  simp

theorem realPlaneCuspidalRep_radical (degree : ℕ) (cusp : CuspidalRepresentation)
    (element : RealPlaneRadical) (values : cuspidalTensorValues cusp (HomogeneousPoly degree)) :
    (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl element) values =
      cuspidalTensorMap cusp ((realUpperRadicalRep degree).ρ element) values := by
  apply Subtype.ext
  funext argument
  rw [realPlaneCuspidalRep_apply, realPlaneMatrix_inl]
  change normPower (GeneralLinearGroup.det (atInfinity (1 : BinaryRealGL))) (((degree : ℂ) + 3) / 2) •
      realCoefficientComponent degree trivialCharacter (realPlaneRadicalMatrix element)
        (values.val (argument * atInfinity (1 : BinaryRealGL))) = _
  rw [atInfinity_one, map_one, normPower_one, one_smul, mul_one]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
