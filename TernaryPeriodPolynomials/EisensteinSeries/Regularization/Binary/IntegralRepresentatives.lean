module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.PrincipalLevel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem binary_integral_finite_representatives :
    ∃ representatives : Finset (GeneralLinearGroup (Fin 2) IntegralAdeles),
      ∀ matrix : GeneralLinearGroup (Fin 2) IntegralAdeles,
        ∃ representative ∈ representatives,
          GeneralLinearGroup.map integralReduction representative =
            GeneralLinearGroup.map integralReduction matrix := by
  classical
  let reduction := GeneralLinearGroup.map (n := Fin 2) integralReduction
  let representative (residue : Set.range reduction) : GeneralLinearGroup (Fin 2) IntegralAdeles :=
    residue.property.choose
  refine ⟨(Set.finite_range representative).toFinset, ?_⟩
  intro matrix
  let residue : Set.range reduction := ⟨reduction matrix, ⟨matrix, rfl⟩⟩
  refine ⟨representative residue, ?_, ?_⟩
  · simp only [Set.Finite.mem_toFinset]
    exact ⟨residue, rfl⟩
  · exact residue.property.choose_spec

theorem binaryIntegral_same_reduction_quotient_mem
    (first second : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (same : GeneralLinearGroup.map integralReduction first = GeneralLinearGroup.map integralReduction second) :
    GeneralLinearGroup.map integralEmbedding (first⁻¹ * second) ∈ binaryPrincipalLevel := by
  refine ⟨first⁻¹ * second, ?_, rfl⟩
  change GeneralLinearGroup.map integralReduction (first⁻¹ * second) = 1
  rw [map_mul, map_inv, same, inv_mul_cancel]

theorem binaryPrincipalLevel_integral_conjugate_mem
    (matrix : GeneralLinearGroup (Fin 2) IntegralAdeles) (element : binaryPrincipalLevel) :
    (GeneralLinearGroup.map integralEmbedding matrix)⁻¹ * element.val *
      GeneralLinearGroup.map integralEmbedding matrix ∈ binaryPrincipalLevel := by
  obtain ⟨integralElement, reduced, represents⟩ := element.property
  refine ⟨matrix⁻¹ * integralElement * matrix, ?_, ?_⟩
  · change GeneralLinearGroup.map integralReduction (matrix⁻¹ * integralElement * matrix) = 1
    change GeneralLinearGroup.map integralReduction integralElement = 1 at reduced
    rw [map_mul, map_mul, map_inv, reduced, mul_one, inv_mul_cancel]
  · rw [map_mul, map_mul, map_inv, represents]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
