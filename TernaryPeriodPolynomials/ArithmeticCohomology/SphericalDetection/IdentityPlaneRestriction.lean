module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalCoinvariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleConjugation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.DeterminantGroupH2

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem upperLeviLatticeInput_neg_one (element : RadicalLattice) :
    upperLeviLatticeInput (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) element = element⁻¹ := by
  have inverse : (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ))⁻¹ =
      GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ) := by
    rw [← map_inv]
    norm_num
  apply Multiplicative.toAdd.injective
  simp [upperLeviLatticeInput, inverse, GeneralLinearGroup.coe_scalar]
  rfl

theorem identityPlaneLevi_neg_one_conjugates (radical : RadicalLattice) :
    (identityPlaneLeviSection (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)))⁻¹ *
        identityPlaneRadicalInclusion radical * identityPlaneLeviSection (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) =
      identityPlaneRadicalInclusion radical⁻¹ := by
  apply Subtype.ext
  change (arithmeticLevi (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)))⁻¹ *
      upperRadicalLattice radical * arithmeticLevi (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) = upperRadicalLattice radical⁻¹
  rw [mul_assoc, upperLeviLatticeInput_conjugation, inv_mul_cancel_left, upperLeviLatticeInput_neg_one]

/-- Every identity-plane class in odd degree has zero restriction to the actual upper lattice. -/
theorem identityPlaneTwoCocycle_restriction_zero (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRep degree)) :
    groupCohomology.H2π (upperRadicalLatticeRep degree)
      (twoCocycleRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree) cycle) = 0 := by
  apply (upperRadicalTwoCocycle_H2_zero_iff degree positive
    (twoCocycleRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree) cycle)).mpr
  exact twoCocycle_projected_alternation_zero identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree)
    (binaryHomogeneousRestrict degree) (binaryHomogeneousRestrict_upperLattice degree)
    (identityPlaneLeviSection (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)))
    identityPlaneLevi_neg_one_conjugates (binaryHomogeneousRestrict_scalar_neg_one degree odd)
    cycle radicalLatticeFirst radicalLatticeSecond

theorem identityPlaneH2_restriction_zero (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cohomology : groupCohomology.H2 (identityPlaneCoefficientRep degree)) :
    twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree) cohomology = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (identityPlaneCoefficientRep degree) cohomology
  rw [twoCohomologyRestriction_apply]
  exact identityPlaneTwoCocycle_restriction_zero degree positive odd cycle

def identityPlaneH2ToRestrictionKernel (degree : ℕ) (positive : 0 < degree) (odd : Odd degree) :
    groupCohomology.H2 (identityPlaneCoefficientRep degree) →ₗ[ℂ]
      (twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree)).ker :=
  LinearMap.id.codRestrict _ (identityPlaneH2_restriction_zero degree positive odd)

/-- In odd degree the binary edge is defined on every source H2 class. -/
def identityPlaneFullBinaryEdge (degree : ℕ) (positive : 0 < degree) (odd : Odd degree) :
    groupCohomology.H2 (identityPlaneCoefficientRep degree) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (degree + 1) (-1)) :=
  (identityPlaneBinaryEdge degree).comp (identityPlaneH2ToRestrictionKernel degree positive odd)

theorem identityPlaneFullBinaryEdge_injective (degree : ℕ) (positive : 0 < degree) (odd : Odd degree) :
    Function.Injective (identityPlaneFullBinaryEdge degree positive odd) := by
  intro first second equality
  have kernels := identityPlaneBinaryEdge_injective degree equality
  exact congrArg Subtype.val kernels

theorem identityPlaneFullBinaryEdge_zero_iff (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cohomology : groupCohomology.H2 (identityPlaneCoefficientRep degree)) :
    identityPlaneFullBinaryEdge degree positive odd cohomology = 0 ↔ cohomology = 0 :=
  LinearMap.map_eq_zero_iff _ (identityPlaneFullBinaryEdge_injective degree positive odd)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
