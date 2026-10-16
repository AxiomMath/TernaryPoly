module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.LowestCuspForm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ModularFiniteIndexDimension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

instance binaryRealPrincipalLevel_finiteRelIndex :
    binaryRealPrincipalLevel.IsFiniteRelIndex (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range := by
  constructor
  rw [binaryRealPrincipalLevel, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]
  exact Subgroup.finiteIndex_iff.mp inferInstance

instance binaryRealPrincipalLevel_modular_finiteDimensional (weight : ℤ) :
    FiniteDimensional ℂ (ModularForm binaryRealPrincipalLevel weight) :=
  modular_finite_dimensional_of_finite_index binaryRealPrincipalLevel weight

instance binaryRealPrincipalLevel_cusp_finiteDimensional (weight : ℤ) :
    FiniteDimensional ℂ (CuspForm binaryRealPrincipalLevel weight) :=
  FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
