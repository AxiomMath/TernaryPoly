module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.InvariantCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CentralGroupH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem arithmeticBinaryRep_scalar_neg_one (degree : ℕ) (odd : Odd degree)
    (polynomial : Binary.HomogeneousPoly degree) :
    (arithmeticBinaryRep degree (-1)).ρ (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) polynomial =
      (-1 : ℂ) • polynomial := by
  change Binary.homogeneousAction degree (-1)
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ))) polynomial = _
  rw [GeneralLinearGroup.map_scalar, binary_homogeneousAction_scalar]
  have power : (-1 : ℂ) ^ (degree + 2) = -1 := by
    rw [pow_add, odd.neg_one_pow]
    norm_num
  simpa using congrArg (fun scalar : ℂ => scalar • polynomial) power

theorem arithmeticBinaryH2_zero_of_odd (degree : ℕ) (odd : Odd degree)
    (cohomology : groupCohomology.H2 (arithmeticBinaryRep degree (-1))) : cohomology = 0 :=
  groupH2_zero_of_central_scalar (arithmeticBinaryRep degree (-1))
    (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) (GeneralLinearGroup.scalar_commute (-1))
    (-1) (by norm_num) (arithmeticBinaryRep_scalar_neg_one degree odd) cohomology

theorem goodLineInvariantH2_zero_of_odd (degree : ℕ) (odd : Odd degree)
    (cohomology : groupCohomology.H2 (splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRep degree))) :
    cohomology = 0 := by
  obtain ⟨binary_class, rfl⟩ := (ConcreteCategory.bijective_of_isIso (goodLineInvariantH2Iso degree).hom).surjective cohomology
  rw [arithmeticBinaryH2_zero_of_odd degree odd binary_class, map_zero]

theorem goodLineBinaryEdge_injective_of_odd (degree : ℕ) (positive : 0 < degree) (odd : Odd degree) :
    Function.Injective (goodLineBinaryEdge degree positive) :=
  goodLineBinaryEdge_injective_of_invariant_H2_zero degree positive (goodLineInvariantH2_zero_of_odd degree odd)

/-- The remaining source inflation comes from one fixed determinant-character coefficient module. -/
def identityPlaneDeterminantInflation (degree : ℕ) :
    groupCohomology.H2 arithmeticDeterminantRep →ₗ[ℂ] groupCohomology.H2 (identityPlaneCoefficientRep degree) :=
  (splitInvariantInflation identityPlaneSplitting (identityPlaneCoefficientRep degree)).comp
    (identityPlaneInvariantH2Iso degree).hom.hom

theorem identityPlaneBinaryEdge_zero_iff_determinantInflation (degree : ℕ)
    (cohomology : (twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree)).ker) :
    identityPlaneBinaryEdge degree cohomology = 0 ↔
      ∃ determinant_class : groupCohomology.H2 arithmeticDeterminantRep,
        identityPlaneDeterminantInflation degree determinant_class = cohomology.val := by
  rw [identityPlaneBinaryEdge_zero_iff_inflation]
  constructor
  · rintro ⟨levi_class, equality⟩
    obtain ⟨determinant_class, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (identityPlaneInvariantH2Iso degree).hom).surjective levi_class
    exact ⟨determinant_class, equality⟩
  · rintro ⟨determinant_class, equality⟩
    exact ⟨(identityPlaneInvariantH2Iso degree).hom determinant_class, equality⟩

theorem identityPlaneBinaryEdge_injective_of_determinant_H2_zero (degree : ℕ)
    (vanishing : ∀ cohomology : groupCohomology.H2 arithmeticDeterminantRep, cohomology = 0) :
    Function.Injective (identityPlaneBinaryEdge degree) := by
  apply identityPlaneBinaryEdge_injective_of_invariant_H2_zero
  intro cohomology
  obtain ⟨determinant_class, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso (identityPlaneInvariantH2Iso degree).hom).surjective cohomology
  rw [vanishing determinant_class, map_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
