module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.InvariantH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.TrivialH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.GroupLowCohomology

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def integralDeterminantSection : ℤˣ →* GeneralLinearGroup (Fin 2) ℤ where
  toFun unit :=
    { val := !![unit.val, 0; 0, 1]
      inv := !![(unit⁻¹).val, 0; 0, 1]
      val_inv := by
        ext row column
        fin_cases row <;> fin_cases column <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ← Units.val_mul]
      inv_val := by
        ext row column
        fin_cases row <;> fin_cases column <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ← Units.val_mul] }
  map_one' := by
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;> simp
  map_mul' first second := by
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem integralDeterminantSection_det (unit : ℤˣ) : GeneralLinearGroup.det (integralDeterminantSection unit) = unit := by
  apply Units.ext
  change Matrix.det !![unit.val, 0; 0, 1] = unit.val
  simp [Matrix.det_fin_two]

theorem integralSpecialLinear_range :
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) ℤ →* GeneralLinearGroup (Fin 2) ℤ).range =
      GeneralLinearGroup.det.ker := by
  ext matrix
  constructor
  · rintro ⟨element, rfl⟩
    exact SpecialLinearGroup.coeToGL_det element
  · intro determinant
    have value : matrix.val.det = 1 := congrArg Units.val determinant
    refine ⟨⟨matrix.val, value⟩, ?_⟩
    apply Units.ext
    rfl

def integralDeterminantExtension :
    GroupExtension (SpecialLinearGroup (Fin 2) ℤ) (GeneralLinearGroup (Fin 2) ℤ) ℤˣ :=
  ⟨SpecialLinearGroup.toGL, GeneralLinearGroup.det, SpecialLinearGroup.toGL_injective,
    integralSpecialLinear_range, fun unit => ⟨integralDeterminantSection unit, integralDeterminantSection_det unit⟩⟩

def integralDeterminantSplitting : integralDeterminantExtension.Splitting :=
  ⟨integralDeterminantSection, integralDeterminantSection_det⟩

theorem arithmeticDeterminantCharacter_specialLinear (element : SpecialLinearGroup (Fin 2) ℤ) :
    arithmeticDeterminantCharacter (SpecialLinearGroup.toGL element) = 1 := by
  change Binary.determinantCharacter (-1)
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL element)) = 1
  unfold Binary.determinantCharacter
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  have determinant : ((element.val).map (Int.castRingHom ℂ)).det = 1 := by
    have equality := (Int.castRingHom ℂ).map_det element.val
    rw [Matrix.SpecialLinearGroup.det_coe element, map_one] at equality
    exact equality.symm
  change (((element.val).map (Int.castRingHom ℂ)).det) ^ (-1 : ℤ) = 1
  rw [determinant, one_zpow]

theorem arithmeticDeterminantRep_specialLinear_trivial (element : SpecialLinearGroup (Fin 2) ℤ)
    (vector : Rep.res SpecialLinearGroup.toGL arithmeticDeterminantRep) :
    (Rep.res SpecialLinearGroup.toGL arithmeticDeterminantRep).ρ element vector = vector := by
  change ℂ at vector
  change arithmeticDeterminantCharacter (SpecialLinearGroup.toGL element) * (vector : ℂ) = vector
  rw [arithmeticDeterminantCharacter_specialLinear, one_mul]

theorem arithmeticDeterminantH2_zero (cohomology : groupCohomology.H2 arithmeticDeterminantRep) : cohomology = 0 := by
  apply splitRestriction_injective_of_finite_quotient integralDeterminantSplitting arithmeticDeterminantRep
  rw [map_zero]
  exact modularTrivialH2_zero (Rep.res SpecialLinearGroup.toGL arithmeticDeterminantRep)
    arithmeticDeterminantRep_specialLinear_trivial _

theorem identityPlaneInvariantH2_zero (degree : ℕ)
    (cohomology : groupCohomology.H2 (splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRep degree))) :
    cohomology = 0 := by
  obtain ⟨determinant_class, rfl⟩ :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso (identityPlaneInvariantH2Iso degree).hom).surjective cohomology
  rw [arithmeticDeterminantH2_zero determinant_class, map_zero]

theorem identityPlaneBinaryEdge_injective (degree : ℕ) : Function.Injective (identityPlaneBinaryEdge degree) :=
  identityPlaneBinaryEdge_injective_of_determinant_H2_zero degree arithmeticDeterminantH2_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
