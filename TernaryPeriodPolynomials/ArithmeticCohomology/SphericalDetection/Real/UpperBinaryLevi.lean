module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperBinaryNormalForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalLeviCocycles

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem polynomialPlaneLevi_last_mul (matrix : Binary.GL2) (polynomial : Poly) :
    action (-1) (planeLevi matrix 1) (X 2 * polynomial) =
      X 2 * action (-1) (planeLevi matrix 1) polynomial := by
  have last : substitute (planeLevi matrix 1)⁻¹.val (X 2) = X 2 := by
    rw [planeLevi_inverse]
    simp [substitute_X, linearForm, planeLevi, planeBlock, Fin.sum_univ_three]
  rw [action_apply, map_mul, last, action_apply, mul_smul_comm]

theorem homogeneousLastMultiply_realLevi (degree : ℕ) (matrix : BinaryRealGL)
    (polynomial : HomogeneousPoly degree) :
    homogeneousLastMultiply degree
        (realCoefficientComponent degree trivialCharacter (planeLevi matrix 1) polynomial) =
      realCoefficientComponent (degree + 1) trivialCharacter (planeLevi matrix 1)
        (homogeneousLastMultiply degree polynomial) := by
  rw [realCoefficientComponent_trivial, realCoefficientComponent_trivial, map_planeLevi_one]
  apply Subtype.ext
  exact (polynomialPlaneLevi_last_mul _ polynomial.val).symm

theorem binaryHomogeneousLift_realLevi (degree : ℕ) (matrix : BinaryRealGL)
    (polynomial : Binary.HomogeneousPoly degree) :
    binaryHomogeneousLift degree
        (Binary.homogeneousAction degree (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix) polynomial) =
      realCoefficientComponent degree trivialCharacter (planeLevi matrix 1)
        (binaryHomogeneousLift degree polynomial) := by
  rw [realCoefficientComponent_trivial, map_planeLevi_one]
  apply Subtype.ext
  change binaryPolynomialLift (Binary.action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix) polynomial.val) =
    action (-1) (planeLevi (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix) 1) (binaryPolynomialLift polynomial.val)
  simpa only [Units.val_one, one_zpow, one_smul] using
    (action_planeLevi_lift (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix) 1 polynomial.val).symm

theorem realUpperBinaryValue_levi (degree : ℕ) (matrix : BinaryRealGL) (element : RealPlaneRadical)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    realUpperBinaryValue degree element
        (Binary.homogeneousAction (degree + 1) (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix) polynomial) =
      realCoefficientComponent degree trivialCharacter (planeLevi matrix 1)
        (realUpperBinaryValue degree (realRadicalInverseLevi matrix element) polynomial) := by
  have group_commute := congrArg realPlaneMatrix (realRadicalInverseLevi_product matrix element)
  simp only [map_mul, realPlaneMatrix_inl, realPlaneMatrix_inr] at group_commute
  have coefficient_commute := congrArg (realCoefficientComponent (degree + 1) trivialCharacter) group_commute
  rw [map_mul, map_mul] at coefficient_commute
  have value_commute := congrArg
    (fun operator : Module.End ℂ (HomogeneousPoly (degree + 1)) => operator (binaryHomogeneousLift (degree + 1) polynomial))
    coefficient_commute
  apply homogeneousLastMultiply_injective degree
  rw [realUpperBinaryValue_multiply, homogeneousLastMultiply_realLevi, realUpperBinaryValue_multiply,
    binaryHomogeneousLift_realLevi, map_sub]
  exact congrArg (fun value => realCoefficientComponent (degree + 1) trivialCharacter (planeLevi matrix 1)
    (binaryHomogeneousLift (degree + 1) polynomial) - value) value_commute

end TernaryPeriodPolynomials.SphericalDetection.Helpers
