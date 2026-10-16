module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Theta.Invariance
public import Mathlib.MeasureTheory.Group.FundamentalDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

instance rationalBinaryCountable : Countable BinaryRationalGL := by
  let _ : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  exact Function.Injective.countable (f := Units.val) Units.val_injective

instance frameCountable : Countable Frame := by
  let _ : Countable (Rectangular ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 2 → ℚ))
  infer_instance

scoped instance rationalAction : MulAction BinaryRationalGL BinaryAdelicGL :=
  MulAction.compHom BinaryAdelicGL (GeneralLinearGroup.map rationalAdele)

theorem rational_smul (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    rational • binary = GeneralLinearGroup.map rationalAdele rational * binary := rfl

scoped instance rationalMeasurable : MeasurableConstSMul BinaryRationalGL BinaryAdelicGL :=
  ⟨fun _ => measurable_const.mul measurable_id⟩

scoped instance rationalInvariant : SMulInvariantMeasure BinaryRationalGL BinaryAdelicGL BinaryHaar.measure :=
  ⟨fun rational _ _ => measure_preimage_mul BinaryHaar.measure (GeneralLinearGroup.map rationalAdele rational) _⟩

noncomputable def weightedTerm {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (frame : Frame) (binary : BinaryAdelicGL) : ℂ :=
  term test point binary frame * innerCharacter data parameter (GeneralLinearGroup.det binary) *
    data.cusp.realize vector binary

theorem weightedTerm_parameterize {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (flag : Flags .plane)
    (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    weightedTerm data test vector parameter point (FrameUnfolding.parameterize (flag, rational)) binary =
      kernel test (rationalGroup flag.out⁻¹ * point) (rational • binary) *
        innerCharacter data parameter (GeneralLinearGroup.det (rational • binary)) *
          data.cusp.realize vector (rational • binary) := by
  have rationalValue : innerCharacter data parameter
      (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact ThetaInvariance.innerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  rw [weightedTerm, term_parameterize, rational_smul, map_mul, map_mul, rationalValue, one_mul,
    data.cusp.leftRational]

theorem raw_unfold {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (flag : Flags .plane)
    (domain : Set BinaryAdelicGL) (fundamental : IsFundamentalDomain BinaryRationalGL domain BinaryHaar.measure)
    (integrable : Integrable (fun binary => kernel test (rationalGroup flag.out⁻¹ * point) binary *
      innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary) BinaryHaar.measure) :
    raw test (innerCharacter data parameter) data.cusp vector (rationalGroup flag.out⁻¹ * point) =
      ∑' rational : BinaryRationalGL, ∫ binary in domain,
        weightedTerm data test vector parameter point (FrameUnfolding.parameterize (flag, rational)) binary
          ∂BinaryHaar.measure := by
  rw [raw, fundamental.integral_eq_tsum'' _ integrable]
  simp only [weightedTerm_parameterize]

theorem integrand_eq_tsum {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    ThetaInvariance.integrand data test vector parameter point binary =
      ∑' frame : Frame, weightedTerm data test vector parameter point frame binary := by
  simp only [ThetaInvariance.integrand, theta, weightedTerm, tsum_mul_right]

theorem integral_theta_unfold {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL)
    (domain : Set BinaryAdelicGL) (fundamental : IsFundamentalDomain BinaryRationalGL domain BinaryHaar.measure)
    (termIntegrable : ∀ frame, IntegrableOn (weightedTerm data test vector parameter point frame) domain BinaryHaar.measure)
    (absolute : Summable (fun frame => ∫ binary in domain,
      ‖weightedTerm data test vector parameter point frame binary‖ ∂BinaryHaar.measure))
    (rawIntegrable : ∀ flag : Flags .plane, Integrable (fun binary =>
      kernel test (rationalGroup flag.out⁻¹ * point) binary * innerCharacter data parameter (GeneralLinearGroup.det binary) *
        data.cusp.realize vector binary) BinaryHaar.measure) :
    ∫ binary in domain, ThetaInvariance.integrand data test vector parameter point binary ∂BinaryHaar.measure =
      ∑' flag : Flags .plane, raw test (innerCharacter data parameter) data.cusp vector (rationalGroup flag.out⁻¹ * point) := by
  have integralSummable : Summable (fun frame => ∫ binary in domain,
      weightedTerm data test vector parameter point frame binary ∂BinaryHaar.measure) :=
    absolute.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
  simp only [integrand_eq_tsum]
  rw [← integral_tsum_of_summable_integral_norm termIntegrable absolute,
    FrameUnfolding.tsum_unfold _ integralSummable]
  congr 1
  funext flag
  exact (raw_unfold data test vector parameter point flag domain fundamental (rawIntegrable flag)).symm

theorem outer_rational_left {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (point : AdelicGL) (rational : RationalGL3) :
    outerCharacter data parameter (GeneralLinearGroup.det (rationalGroup rational * point)) =
      outerCharacter data parameter (GeneralLinearGroup.det point) := by
  have rationalValue : outerCharacter data parameter (GeneralLinearGroup.det (rationalGroup rational)) = 1 := by
    change outerCharacter data parameter (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1
    rw [GeneralLinearGroup.map_det]
    exact ThetaInvariance.outerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  rw [map_mul, map_mul, rationalValue, one_mul]

theorem eisenstein_integral_identity {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL)
    (domain : Set BinaryAdelicGL) (fundamental : IsFundamentalDomain BinaryRationalGL domain BinaryHaar.measure)
    (termIntegrable : ∀ frame, IntegrableOn (weightedTerm data test vector parameter point frame) domain BinaryHaar.measure)
    (absolute : Summable (fun frame => ∫ binary in domain,
      ‖weightedTerm data test vector parameter point frame binary‖ ∂BinaryHaar.measure))
    (rawIntegrable : ∀ flag : Flags .plane, Integrable (fun binary =>
      kernel test (rationalGroup flag.out⁻¹ * point) binary * innerCharacter data parameter (GeneralLinearGroup.det binary) *
        data.cusp.realize vector binary) BinaryHaar.measure) :
    ∑' flag, eisensteinSummand (sectionFunction data test vector) parameter point flag =
      outerCharacter data parameter (GeneralLinearGroup.det point) *
        ∫ binary in domain, ThetaInvariance.integrand data test vector parameter point binary ∂BinaryHaar.measure := by
  simp only [eisensteinSummand, sectionFunction, outer_rational_left]
  rw [tsum_mul_left, integral_theta_unfold data test vector parameter point domain fundamental
    termIntegrable absolute rawIntegrable]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding
