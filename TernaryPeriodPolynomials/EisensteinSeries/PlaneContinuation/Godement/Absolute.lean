module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FundamentalIntegration

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementAbsolute

def rawKernel {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) : ℂ :=
  kernel test point binary * innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary

theorem weightedTerm_integrable {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL)
    (rawIntegrable : ∀ flag : Flags .plane, Integrable
      (rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point)) BinaryHaar.measure)
    (frame : Frame) :
    IntegrableOn (weightedTerm data test vector parameter point frame) BinaryFundamentalDomain.domain BinaryHaar.measure := by
  obtain ⟨⟨flag, rational⟩, rfl⟩ := FrameUnfolding.parameterize_surjective frame
  have translated := (measurePreserving_smul rational BinaryHaar.measure).integrable_comp_of_integrable (rawIntegrable flag)
  have equality : weightedTerm data test vector parameter point (FrameUnfolding.parameterize (flag, rational)) =
      rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point) ∘ (fun binary => rational • binary) :=
    funext (fun binary => weightedTerm_parameterize data test vector parameter point flag rational binary)
  rw [equality]
  exact translated.integrableOn

theorem norm_hasSum {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (flag : Flags .plane)
    (rawIntegrable : Integrable (rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point)) BinaryHaar.measure) :
    HasSum (fun rational : BinaryRationalGL => ∫ binary in BinaryFundamentalDomain.domain,
      ‖weightedTerm data test vector parameter point (FrameUnfolding.parameterize (flag, rational)) binary‖ ∂BinaryHaar.measure)
      (∫ binary, ‖rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure) := by
  simpa only [rawKernel, weightedTerm_parameterize] using
    FundamentalIntegration.hasSum_norm_translates BinaryFundamentalDomain.domain_fundamental rawIntegrable

theorem absolute_iff {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL)
    (rawIntegrable : ∀ flag : Flags .plane, Integrable
      (rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point)) BinaryHaar.measure) :
    Summable (fun frame => ∫ binary in BinaryFundamentalDomain.domain,
      ‖weightedTerm data test vector parameter point frame binary‖ ∂BinaryHaar.measure) ↔
    Summable (fun flag : Flags .plane => ∫ binary,
      ‖rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure) := by
  rw [FrameUnfolding.summable_iff]
  rw [summable_prod_of_nonneg (fun _ => integral_nonneg (fun _ => norm_nonneg _))]
  have summable (flag : Flags .plane) := (norm_hasSum data test vector parameter point flag (rawIntegrable flag)).summable
  have equality (flag : Flags .plane) := (norm_hasSum data test vector parameter point flag (rawIntegrable flag)).tsum_eq
  simp only [equality, summable, implies_true, true_and]

theorem eisenstein_integral_identity {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL)
    (rawIntegrable : ∀ flag : Flags .plane, Integrable
      (rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point)) BinaryHaar.measure)
    (absolute : Summable (fun flag : Flags .plane => ∫ binary,
      ‖rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure)) :
    ∑' flag, eisensteinSummand (sectionFunction data test vector) parameter point flag =
      outerCharacter data parameter (GeneralLinearGroup.det point) *
        ∫ binary in BinaryFundamentalDomain.domain, ThetaInvariance.integrand data test vector parameter point binary ∂BinaryHaar.measure :=
  BinaryFundamentalDomain.eisenstein_integral_identity data test vector parameter point
    (weightedTerm_integrable data test vector parameter point rawIntegrable)
    ((absolute_iff data test vector parameter point rawIntegrable).mpr absolute) rawIntegrable

theorem eisenstein_hasSum {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL)
    (rawIntegrable : ∀ flag : Flags .plane, Integrable
      (rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point)) BinaryHaar.measure)
    (absolute : Summable (fun flag : Flags .plane => ∫ binary,
      ‖rawKernel data test vector parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure)) :
    HasSum (fun flag => eisensteinSummand (sectionFunction data test vector) parameter point flag)
      (outerCharacter data parameter (GeneralLinearGroup.det point) *
        ∫ binary in BinaryFundamentalDomain.domain, ThetaInvariance.integrand data test vector parameter point binary ∂BinaryHaar.measure) := by
  have rawSummable : Summable (fun flag : Flags .plane =>
      raw test (innerCharacter data parameter) data.cusp vector (rationalGroup flag.out⁻¹ * point)) :=
    absolute.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
  have summable : Summable (fun flag => eisensteinSummand (sectionFunction data test vector) parameter point flag) := by
    simpa only [eisensteinSummand, sectionFunction, GodementUnfolding.outer_rational_left] using
      rawSummable.mul_left (outerCharacter data parameter (GeneralLinearGroup.det point))
  rw [← eisenstein_integral_identity data test vector parameter point rawIntegrable absolute]
  exact summable.hasSum

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementAbsolute
