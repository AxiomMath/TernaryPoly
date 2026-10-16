module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.FlagStabilizers
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Plane.SectionPairing
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.AverageDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem normalized_eisensteinSummand_of_representative
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (representative : RationalGL3) (matrix : AdelicGL) :
    eisensteinSummand (unitaryNormalize degree family) parameter matrix (QuotientGroup.mk representative) =
      unitaryNormalize degree family parameter (rationalGroup representative⁻¹ * matrix) := by
  rw [unitaryNormalize_eisensteinSummand, eisensteinSummand_of_representative (flat.1 _)]
  simp only [unitaryNormalize, map_mul, normPower_mul, rationalGroup, GeneralLinearGroup.map_det,
    normPower_rational, one_mul]

theorem normalized_eisensteinSummand_representative_slice
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (representative : SpecialLinearGroup (Fin 3) ℤ)
    (integral : GL3 IntegralAdeles) (matrix : RealSL3) :
    eisensteinSummand (unitaryNormalize degree family) parameter
      (realSpecialIntegralSlice integral (SpecialLinearGroup.map (Int.castRingHom ℝ) representative * matrix))
      (QuotientGroup.mk (integerSpecialLinearRationalHom representative)) =
      unitaryNormalize degree family parameter
        (realSpecialIntegralSlice (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles)
          (SpecialLinearGroup.toGL representative⁻¹) * integral) matrix) := by
  rw [normalized_eisensteinSummand_of_representative flat]
  have identity := integer_inverse_slice_identity representative⁻¹ integral matrix
  simp only [map_inv, inv_inv] at identity
  simpa only [integerSpecialLinearRationalHom, MonoidHom.comp_apply, map_inv] using
    congrArg (unitaryNormalize degree family parameter) identity

theorem normalizedBoundaryResidueAverage_integer_forward
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (representative : SpecialLinearGroup (Fin 3) ℤ) (integral : GL3 IntegralAdeles)
    (kernel : RealSL3 → ℂ) (matrix : RealSL3) :
    normalizedBoundaryResidueAverage degree continuation integral kernel
      (SpecialLinearGroup.map (Int.castRingHom ℝ) representative * matrix) =
      normalizedBoundaryResidueAverage degree continuation
        (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) (SpecialLinearGroup.toGL representative⁻¹) * integral)
        kernel matrix := by
  simpa only [map_inv, inv_inv] using normalizedBoundaryResidueAverage_integer_inverse
    flat continuation_spec representative⁻¹ integral kernel matrix

theorem normalized_flag_representative_pairing_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (parameter : ℂ) (representative : SpecialLinearGroup (Fin 3) ℤ) (integral : GL3 IntegralAdeles)
    {kernel : RealSL3 → ℂ} (kernel_measurable : Measurable kernel)
    (kernel_integrable : Integrable kernel realSpecialLinearHaar) :
    (∫ matrix in (fun point : RealSL3 => SpecialLinearGroup.map (Int.castRingHom ℝ) representative * point) ''
      principalPlaneDomain,
      eisensteinSummand (unitaryNormalize degree family) parameter (realSpecialIntegralSlice integral matrix)
        (QuotientGroup.mk (integerSpecialLinearRationalHom representative)) *
        star (normalizedBoundaryResidueAverage degree continuation integral kernel matrix) ∂realSpecialLinearHaar) = 0 := by
  rw [(measurePreserving_mul_left realSpecialLinearHaar
    (SpecialLinearGroup.map (Int.castRingHom ℝ) representative)).setIntegral_image_emb
      (MeasurableEquiv.mulLeft (SpecialLinearGroup.map (Int.castRingHom ℝ) representative)).measurableEmbedding]
  simp only [normalized_eisensteinSummand_representative_slice flat,
    normalizedBoundaryResidueAverage_integer_forward flat continuation_spec]
  exact normalized_section_residue_average_plane_pairing_zero flat continuation_spec parameter _
    kernel_measurable kernel_integrable

noncomputable def principalFlagDomain (flag : Flags .plane) : Set RealSL3 :=
  (fun matrix : RealSL3 => SpecialLinearGroup.map (Int.castRingHom ℝ) (planeFlagSpecialLinearRepresentative flag) * matrix) ''
    principalPlaneDomain

theorem principalFlagDomain_isFundamental (flag : Flags .plane) :
    IsFundamentalDomain (MulAction.stabilizer principalRealSpecialLinear flag)
      (principalFlagDomain flag) realSpecialLinearHaar := by
  have fundamental := principalFlagRepresentativeDomain_isFundamental (planeFlagSpecialLinearRepresentative flag)
  rw [planeFlagSpecialLinearRepresentative_spec] at fundamental
  exact fundamental

theorem normalized_flag_stabilizer_pairing_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (parameter : ℂ) (integral : GL3 IntegralAdeles) {kernel : RealSL3 → ℂ}
    (kernel_measurable : Measurable kernel) (kernel_integrable : Integrable kernel realSpecialLinearHaar)
    (flag : Flags .plane) :
    (∫ matrix in principalFlagDomain flag,
      eisensteinSummand (unitaryNormalize degree family) parameter (realSpecialIntegralSlice integral matrix) flag *
        star (normalizedBoundaryResidueAverage degree continuation integral kernel matrix) ∂realSpecialLinearHaar) = 0 := by
  have zero := normalized_flag_representative_pairing_zero flat continuation_spec parameter
    (planeFlagSpecialLinearRepresentative flag) integral kernel_measurable kernel_integrable
  rw [planeFlagSpecialLinearRepresentative_spec] at zero
  exact zero

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
