module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerActions
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.TwoCocycleDetection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LeviPolynomialSubstitution
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

def binaryHomogeneousRestrict (degree : ℕ) : HomogeneousPoly degree →ₗ[ℂ] Binary.HomogeneousPoly degree :=
  (binaryPolynomialRestrict.toLinearMap.comp (homogeneousSubmodule (Fin 3) ℂ degree).subtype).codRestrict _
    (fun polynomial => binaryPolynomialRestrict_homogeneous polynomial.val polynomial.property)

theorem binaryHomogeneousRestrict_apply (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    (binaryHomogeneousRestrict degree polynomial).val = binaryPolynomialRestrict polynomial.val := rfl

theorem binaryHomogeneousRestrict_upperGenerator (degree : ℕ) (coordinate : Fin 2)
    (polynomial : HomogeneousPoly degree) :
    binaryHomogeneousRestrict degree (upperRadicalGenerator degree coordinate polynomial) = 0 := by
  have equality : binaryPolynomialRestrict ((-1 : ℂ) • (X 2 * pderiv coordinate.castSucc polynomial.val)) = 0 := by
    rw [map_smul, map_mul, binaryPolynomialRestrict_X]
    simp
  exact Subtype.ext equality

theorem upperRadicalGenerator_range (degree : ℕ) (positive : 0 < degree) (coordinate : Fin 2) :
    (upperRadicalGenerator degree coordinate).range = (binaryHomogeneousRestrict degree).ker := by
  apply Submodule.ext
  intro polynomial
  constructor
  · rintro ⟨potential, rfl⟩
    exact binaryHomogeneousRestrict_upperGenerator degree coordinate potential
  · intro zero
    have restricted : binaryPolynomialRestrict polynomial.val = 0 := congrArg Subtype.val zero
    obtain ⟨factor, equality⟩ := (binaryPolynomialRestrict_zero_iff_dvd polynomial.val).mp restricted
    have factor_degree : factor.IsHomogeneous (degree - 1) :=
      homogeneous_of_X_mul 2 factor (by rw [← equality]; exact polynomial.property)
    have potential_degree : (polynomialAntiderivative coordinate.castSucc factor).IsHomogeneous degree := by
      convert polynomialAntiderivative_homogeneous coordinate.castSucc factor factor_degree using 1
      omega
    refine ⟨-⟨polynomialAntiderivative coordinate.castSucc factor, potential_degree⟩, ?_⟩
    apply Subtype.ext
    change (-1 : ℂ) • (X 2 * pderiv coordinate.castSucc (-polynomialAntiderivative coordinate.castSucc factor)) = polynomial.val
    rw [map_neg, pderiv_polynomialAntiderivative, mul_neg, neg_one_smul, neg_neg]
    exact equality.symm

theorem upperRadicalLattice_first_range (degree : ℕ) (positive : 0 < degree) :
    ((upperRadicalLatticeRep degree).ρ radicalLatticeFirst - 1).range = (binaryHomogeneousRestrict degree).ker := by
  rw [upperRadicalLatticeRep_first, exp_inst_irrel _ Algebra.toModule]
  exact (nilpotent_difference_range _ degree (upperRadicalGenerator_power_zero degree 0)).trans
    (upperRadicalGenerator_range degree positive 0)

theorem upperRadicalLattice_second_range (degree : ℕ) (positive : 0 < degree) :
    ((upperRadicalLatticeRep degree).ρ radicalLatticeSecond - 1).range = (binaryHomogeneousRestrict degree).ker := by
  rw [upperRadicalLatticeRep_second, exp_inst_irrel _ Algebra.toModule]
  exact (nilpotent_difference_range _ degree (upperRadicalGenerator_power_zero degree 1)).trans
    (upperRadicalGenerator_range degree positive 1)

theorem upperRadicalTwoCocycle_H2_zero_iff (degree : ℕ) (positive : 0 < degree)
    (cycle : groupCohomology.cocycles₂ (upperRadicalLatticeRep degree)) :
    groupCohomology.H2π (upperRadicalLatticeRep degree) cycle = 0 ↔
      binaryHomogeneousRestrict degree (latticeTwoCocycleAlternation (upperRadicalLatticeRep degree) cycle) = 0 := by
  rw [latticeTwoCocycle_H2_zero_iff]
  constructor
  · rintro ⟨alpha, beta, equality⟩
    have first : ((upperRadicalLatticeRep degree).ρ radicalLatticeFirst - 1) beta ∈
        (binaryHomogeneousRestrict degree).ker := by
      rw [← upperRadicalLattice_first_range degree positive]
      exact ⟨beta, rfl⟩
    have second : ((upperRadicalLatticeRep degree).ρ radicalLatticeSecond - 1) alpha ∈
        (binaryHomogeneousRestrict degree).ker := by
      rw [← upperRadicalLattice_second_range degree positive]
      exact ⟨alpha, rfl⟩
    rw [equality]
    exact (binaryHomogeneousRestrict degree).map_sub _ _ |>.trans (by rw [first, second, sub_self])
  · intro zero
    have member : latticeTwoCocycleAlternation (upperRadicalLatticeRep degree) cycle ∈
        ((upperRadicalLatticeRep degree).ρ radicalLatticeFirst - 1).range := by
      rw [upperRadicalLattice_first_range degree positive]
      exact zero
    obtain ⟨beta, equality⟩ := member
    exact ⟨0, beta, by rw [map_zero, sub_zero]; exact equality.symm⟩

theorem binaryPolynomialRestrict_planeUnipotent (first second : ℂ) (polynomial : Poly) :
    binaryPolynomialRestrict (action (-1) (planeUnipotent first second) polynomial) =
      binaryPolynomialRestrict polynomial := by
  have determinant : determinantCharacter (-1) (planeUnipotent first second) = 1 := by
    change ((planeUnipotent first second).val.det) ^ (-1 : ℤ) = 1
    simp [planeUnipotent, Matrix.det_fin_three]
  have substitution : binaryPolynomialRestrict.comp (substitute (planeUnipotent first second)⁻¹.val) =
      binaryPolynomialRestrict := by
    apply MvPolynomial.algHom_ext
    intro coordinate
    fin_cases coordinate <;>
      simp [AlgHom.comp_apply, substitute_X, linearForm, planeUnipotent,
        binaryPolynomialRestrict, Fin.sum_univ_three]
  rw [action_apply, determinant, one_smul]
  exact congrArg (fun hom : Poly →ₐ[ℂ] Binary.Poly => hom polynomial) substitution

theorem binaryHomogeneousRestrict_upperLattice (degree : ℕ) (element : RadicalLattice)
    (polynomial : HomogeneousPoly degree) :
    binaryHomogeneousRestrict degree ((upperRadicalLatticeRep degree).ρ element polynomial) =
      binaryHomogeneousRestrict degree polynomial := by
  rw [upperRadicalLatticeRep_rho]
  change binaryHomogeneousRestrict degree
    (rationalCoefficientComponent degree trivialCharacter
      (planeUnipotent (element.toAdd.1 : ℚ) (element.toAdd.2 : ℚ)) polynomial) = _
  rw [rationalCoefficient_planeUnipotent]
  apply Subtype.ext
  exact binaryPolynomialRestrict_planeUnipotent _ _ polynomial.val

theorem binaryHomogeneousRestrict_arithmeticLevi (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (polynomial : HomogeneousPoly degree) :
    binaryHomogeneousRestrict degree (arithmeticLeviCoefficient degree matrix polynomial) =
      Binary.homogeneousAction degree (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (binaryHomogeneousRestrict degree polynomial) := by
  rw [arithmeticLeviCoefficient_homogeneous]
  apply Subtype.ext
  change binaryPolynomialRestrict (action (-1)
    (planeLevi (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) 1) polynomial.val) = _
  rw [action_apply, planeLevi_determinantCharacter, planeLevi_inverse, map_smul]
  simp only [Units.val_one, one_zpow, mul_one, planeLevi_value]
  rw [restrict_substitute_planeBlock]
  rfl

theorem binaryHomogeneousRestrict_scalar_neg_one (degree : ℕ) (odd : Odd degree)
    (polynomial : HomogeneousPoly degree) :
    binaryHomogeneousRestrict degree
      (arithmeticLeviCoefficient degree (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) polynomial) =
        -binaryHomogeneousRestrict degree polynomial := by
  rw [binaryHomogeneousRestrict_arithmeticLevi, GeneralLinearGroup.map_scalar, binary_homogeneousAction_scalar]
  have power : (-1 : ℂ) ^ (degree + 2) = -1 := by
    rw [pow_add, odd.neg_one_pow]
    norm_num
  have equality := congrArg (fun scalar : ℂ => scalar • binaryHomogeneousRestrict degree polynomial) power
  have negated := equality.trans (neg_one_smul ℂ (binaryHomogeneousRestrict degree polynomial))
  simpa using negated

end TernaryPeriodPolynomials.SphericalDetection.Helpers
