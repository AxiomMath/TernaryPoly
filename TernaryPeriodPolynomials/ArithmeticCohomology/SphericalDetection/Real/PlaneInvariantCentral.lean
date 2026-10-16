module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.InvariantCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneRadicalCoefficients
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneMixedCocycles
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CentralGroupH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CohomologyExactness

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem ternaryCuspidalValues_central (degree : ℕ) (cusp : CuspidalRepresentation)
    (values : cuspidalTensorValues cusp (HomogeneousPoly degree))
    (unit : Adelesˣ) (argument : BinaryAdelicGL) :
    values.val (argument * GeneralLinearGroup.scalar (Fin 2) unit) =
      cusp.centralCharacter unit • values.val argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  obtain ⟨vector, realizes⟩ := values.property (ternaryPolynomialCoefficient degree monomial)
  have central := cusp.central unit vector argument
  rw [GeneralLinearGroup.scalar_commute] at central
  change (values.val (argument * GeneralLinearGroup.scalar (Fin 2) unit)).val.coeff monomial =
    (cusp.centralCharacter unit • (values.val argument).val).coeff monomial
  rw [coeff_smul]
  simpa only [realizes, ternaryPolynomialCoefficient, LinearMap.comp_apply,
    Submodule.subtype_apply, MvPolynomial.lcoeff_apply, smul_eq_mul] using central

theorem realPlaneInvariant_polynomial (degree : ℕ) (cusp : CuspidalRepresentation)
    (values : (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter)).ρ.invariants)
    (argument : BinaryAdelicGL) :
    (values.val.val argument) ∈ (upperRadicalLatticeRep degree).ρ.invariants := by
  change ∀ radical, (upperRadicalLatticeRep degree).ρ radical (values.val.val argument) = values.val.val argument
  intro radical
  have invariant := (Representation.mem_invariants _ _).mp values.property (radicalLatticeReal radical)
  have value := congrArg (fun vector : cuspidalTensorValues cusp (HomogeneousPoly degree) =>
    vector.val argument) invariant
  exact (realPlaneCuspidalRep_latticeRadical degree cusp radical values.val argument).symm.trans value

theorem realPlaneInvariant_positive_scalar (degree : ℕ) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (unit : ℝˣ) (positive : 0 < unit.val)
    (values : (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter)).ρ.invariants) :
    (splitInvariantRepresentation realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter)).ρ
        (GeneralLinearGroup.scalar (Fin 2) unit) values =
      (unit.val : ℂ) ^ (degree + 1) • values := by
  apply Subtype.ext
  apply Subtype.ext
  funext argument
  let tensor : cuspidalTensorValues cusp (HomogeneousPoly degree) := values.val
  change ((realPlaneCuspidalRep degree cusp trivialCharacter).ρ
    (SemidirectProduct.inr (GeneralLinearGroup.scalar (Fin 2) unit)) values.val).val argument = _
  refine (realPlaneCuspidalRep_apply degree cusp trivialCharacter
    (SemidirectProduct.inr (GeneralLinearGroup.scalar (Fin 2) unit)) values.val argument).trans ?_
  rw [realPlaneMatrix_inr]
  change normPower (GeneralLinearGroup.det (atInfinity (GeneralLinearGroup.scalar (Fin 2) unit)))
      (((degree : ℂ) + 3) / 2) •
    realCoefficientComponent degree trivialCharacter (planeLevi (GeneralLinearGroup.scalar (Fin 2) unit) 1)
      (tensor.val (argument * atInfinity (GeneralLinearGroup.scalar (Fin 2) unit))) =
    (unit.val : ℂ) ^ (degree + 1) • tensor.val argument
  rw [binary_scalar_normalizingFactor degree unit positive, atInfinity_scalar,
    ternaryCuspidalValues_central, central_positive unit positive, one_smul,
    realCoefficientComponent_trivial, map_planeLevi_one]
  obtain ⟨scalar, equality⟩ := (upperRadicalInvariant_scalar degree _).mp
    (realPlaneInvariant_polynomial degree cusp values argument)
  apply Subtype.ext
  change (unit.val : ℂ) ^ (degree + 3) •
    action (-1) (planeLevi (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (GeneralLinearGroup.scalar (Fin 2) unit)) 1) (tensor.val argument).val =
    (unit.val : ℂ) ^ (degree + 1) • (tensor.val argument).val
  have cmul : C scalar * (X 2 ^ degree : Poly) = scalar • (X 2 ^ degree : Poly) :=
    (Algebra.smul_def scalar (X 2 ^ degree : Poly)).symm
  rw [equality, cmul, map_smul, action_planeLevi_third_power,
    GeneralLinearGroup.map_scalar]
  have determinant : Binary.determinantCharacter (-1)
      (GeneralLinearGroup.scalar (Fin 2) ((Units.map (algebraMap ℝ ℂ)) unit)) =
      ((unit.val : ℂ) ^ 2)⁻¹ := by
    simp [Binary.determinantCharacter]
  rw [determinant, smul_smul, smul_smul, smul_smul]
  congr 1
  have nonzero : (unit.val : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast unit.ne_zero)
  rw [show degree + 3 = (degree + 1) + 2 by omega, pow_add]
  field_simp

theorem realPlaneInvariant_H2_zero (degree : ℕ) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (cohomology : groupCohomology.H2
      (splitInvariantRepresentation realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter))) :
    cohomology = 0 := by
  let unit : ℝˣ := Units.mk0 2 (by norm_num)
  apply groupH2_zero_of_central_scalar _ (GeneralLinearGroup.scalar (Fin 2) unit)
    (GeneralLinearGroup.scalar_commute unit) ((unit.val : ℂ) ^ (degree + 1))
  · change (2 : ℂ) ^ (degree + 1) ≠ 1
    exact_mod_cast ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega : degree + 1 ≠ 0))
  · exact realPlaneInvariant_positive_scalar degree cusp central_positive unit (by norm_num [unit])

theorem realPlaneCohomologyEdge_injective (degree : ℕ) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1) :
    Function.Injective (splitCohomologyEdge realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter)) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero realPlaneSplitting _
    (realPlaneInvariant_H2_zero degree cusp central_positive)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
