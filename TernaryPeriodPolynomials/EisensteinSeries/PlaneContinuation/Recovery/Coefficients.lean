module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.HilbertConvolution

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoverySupport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteMatrixWeight TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryCoefficients

theorem boxes_continuous (boxes : FlatProfilePackages.Boxes) : Continuous boxes.test := by
  apply continuous_finsetSum
  intro coset _
  exact continuous_const.mul (ZeroConstantThetaDecay.finiteTest_continuous _ _)

theorem finite_orbit (point : AdelicGL) (binary : BinaryFiniteGL) :
    finite (FrameProfile.frame point * (atFinite binary).val) = finite (FrameProfile.frame point) * binary.val := by
  change (FrameProfile.frame point * (atFinite binary).val).map (RingHom.snd ℝ FiniteAdeles) = _
  rw [Matrix.map_mul]
  rfl

theorem finite_orbit_continuous (point : AdelicGL) :
    Continuous (fun binary : BinaryFiniteGL => finite (FrameProfile.frame point * (atFinite binary).val)) := by
  simp only [finite_orbit]
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  simp only [Matrix.mul_apply]
  apply continuous_finsetSum
  intro index _
  exact continuous_const.mul ((continuous_apply column).comp ((continuous_apply index).comp
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) FiniteAdeles))))

def coefficient {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : AdelicGL)
    (key : UniversalFiniteProfiles.Key data) (binary : BinaryFiniteGL) : ℂ :=
  (UniversalFiniteProfiles.boxes data key).test (finite (FrameProfile.frame point * (atFinite binary).val)) *
    innerCharacter data parameter (GeneralLinearGroup.det (atFinite binary))

theorem coefficient_measurable {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : AdelicGL)
    (key : UniversalFiniteProfiles.Key data) : Measurable (coefficient data parameter point key) :=
  ((boxes_continuous _).comp (finite_orbit_continuous point)).measurable.mul
    ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp
      (GeneralLinearGroup.continuous_det.comp atFinite_continuous).measurable)

theorem coefficient_supported {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) (binary : BinaryFiniteGL) (outside : ¬ IntegralMatrix binary) :
    coefficient data parameter point key binary = 0 := by
  have frameOutside : finite (FrameProfile.frame point * (atFinite binary).val) ∉ Set.range CompactFiniteFrames.embedding :=
    fun inside => outside (integralMatrix_of_frame point pointIntegral binary inside)
  rw [coefficient, UniversalFiniteProfiles.boxes_supported data key _ frameOutside, zero_mul]

theorem inner_norm {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (binary : BinaryFiniteGL) :
    ‖innerCharacter data parameter (GeneralLinearGroup.det (atFinite binary))‖ =
      weight binary ^ ((degree : ℝ) / 2 + 3 + parameter.re) := by
  change ‖(data.chi.toMonoidHom _)⁻¹ * normPower _ _‖ = _
  rw [norm_mul, norm_inv, data.chi.unitary, inv_one, one_mul, Helpers.norm_normPower,
    Real.rpow_def_of_pos (weight_pos binary)]
  congr 1
  have exponentEquality :
      (binaryInductionExponent degree .plane parameter + 2 * inductionExponent .plane parameter).re =
        (degree : ℝ) / 2 + 3 + parameter.re := by
    simp [binaryInductionExponent, inductionExponent, Complex.add_re, Complex.mul_re]
    ring
  rw [exponentEquality]
  exact mul_comm _ _

theorem coefficient_bound {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : AdelicGL)
    (key : UniversalFiniteProfiles.Key data) (binary : BinaryFiniteGL) (integral : IntegralMatrix binary) :
    ‖coefficient data parameter point key binary‖ ≤ weight binary ^ 3 := by
  obtain zero | one := UniversalFiniteProfiles.boxes_values data key
    (finite (FrameProfile.frame point * (atFinite binary).val))
  · rw [coefficient, zero, zero_mul, norm_zero]
    exact pow_nonneg (weight_pos binary).le _
  · rw [coefficient, one, one_mul, inner_norm]
    have bound := Real.rpow_le_rpow_of_exponent_ge (weight_pos binary)
      (norm_le_one binary integral) (show (3 : ℝ) ≤ (degree : ℝ) / 2 + 3 + parameter.re by linarith)
    simpa only [show (3 : ℝ) = ((3 : ℕ) : ℝ) from rfl, Real.rpow_natCast] using bound

theorem coefficient_integrable {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) :
    Integrable (coefficient data parameter point key) BinaryProductHaar.finiteMeasure := by
  apply integrable_of_bound _ (coefficient_measurable data parameter point key).aestronglyMeasurable 1
    (coefficient_supported data parameter point pointIntegral key)
  intro binary integral
  simpa only [one_mul] using coefficient_bound data parameter halfPlane point key binary integral

def operator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) : data.cusp.H →L[ℂ] data.cusp.H :=
  FiniteHilbertConvolution.operator data.cusp (coefficient data parameter point key)
    (coefficient_integrable data parameter halfPlane point pointIntegral key)

def projected {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) : data.cusp.H →L[ℂ] data.cusp.H :=
  FiniteHilbertConvolution.projected data.cusp finiteCongruence (coefficient data parameter point key)
    (coefficient_integrable data parameter halfPlane point pointIntegral key)

theorem kernel_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (binary : BinaryFiniteGL) :
    RealBinaryRecovery.kernel induced point (atFinite binary) =
      ∑ key : UniversalFiniteProfiles.Key data, coefficient data parameter point key binary *
        data.cusp.realize (FrameProfile.profile induced (RealFrameChart.adelicFrame
          (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key))
          (IntegralFrameOrbit.realFrame point))) (atFinite binary) := by
  simp only [RealBinaryRecovery.kernel, RealBinaryRecovery.real_mul_finite, ← IntegralFrameOrbit.realFrame_eq,
    coefficient, mul_assoc]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryCoefficients
