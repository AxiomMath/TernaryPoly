module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.BinaryCovariance

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ScalarBinaryIntegral

def cuspIntegrand {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL)
    (coordinates : Adeles × Adeles) : ℂ :=
  data.cusp.realize
    (CuspLift.vector data .plane parameter function induced
      (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument)) binary

theorem integrand_lineLevi {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL)
    (coordinates : Adeles × Adeles) :
    standardIntegrand (fun _ => function) parameter (lineLevi 1 binary * argument)
      coordinates =
      normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .plane parameter) *
        cuspIntegrand data parameter function induced binary argument
          (BinaryGaussian.rowAction binary coordinates) := by
  unfold standardIntegrand
  rw [mul_assoc (weyl⁻¹ : AdelicGL), ← mul_assoc (lineUnipotent _ _),
    HilbertBinaryCovariance.lineUnipotent_lineLevi]
  rw [mul_assoc (lineLevi 1 binary)
    (lineUnipotent (BinaryGaussian.rowAction binary coordinates).1
      (BinaryGaussian.rowAction binary coordinates).2) argument,
    ← mul_assoc (weyl⁻¹ : AdelicGL) (lineLevi 1 binary), weyl_inverse_lineLevi,
    mul_assoc (planeLevi binary 1) (weyl⁻¹ : AdelicGL)]
  rw [← mul_assoc (weyl⁻¹ : AdelicGL)
    (lineUnipotent (BinaryGaussian.rowAction binary coordinates).1
      (BinaryGaussian.rowAction binary coordinates).2) argument]
  let base : AdelicGL := weyl⁻¹ *
    lineUnipotent (BinaryGaussian.rowAction binary coordinates).1
      (BinaryGaussian.rowAction binary coordinates).2 * argument
  change function (binaryLevi .plane binary * base) =
    normPower (GeneralLinearGroup.det binary)
      (binaryInductionExponent degree .plane parameter) *
      data.cusp.realize (CuspLift.vector data .plane parameter function induced base) binary
  exact CuspLiftCovariance.scalar_binary data .plane parameter function induced binary base

theorem integral_lineLevi {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL) :
    (adeleNorm (GeneralLinearGroup.det binary) : ℝ) •
        (∫ coordinates, standardIntegrand (fun _ => function) parameter
          (lineLevi 1 binary * argument) coordinates ∂radicalMeasure) =
      normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .plane parameter) *
        ∫ coordinates, cuspIntegrand data parameter function induced binary argument
          coordinates ∂radicalMeasure := by
  have transform :
      (fun coordinates : Adeles × Adeles => standardIntegrand (fun _ => function) parameter
        (lineLevi 1 binary * argument) coordinates) =
      (fun coordinates => normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .plane parameter) *
        cuspIntegrand data parameter function induced binary argument
          (BinaryGaussian.rowAction binary coordinates)) := by
    funext coordinates
    exact integrand_lineLevi data parameter function induced binary argument coordinates
  have integralEquality := congrArg
    (fun integrand : Adeles × Adeles → ℂ => ∫ coordinates, integrand coordinates ∂radicalMeasure)
    transform
  rw [integralEquality]
  rw [integral_const_mul]
  have scaled := BinaryRowMeasure.integral_row binary
    (cuspIntegrand data parameter function induced binary argument)
  calc
    _ = normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .plane parameter) *
          ((adeleNorm (GeneralLinearGroup.det binary) : ℝ) •
            (∫ coordinates, cuspIntegrand data parameter function induced binary argument
              (BinaryGaussian.rowAction binary coordinates) ∂radicalMeasure)) := by
      simp only [Complex.real_smul]
      ring
    _ = _ := congrArg (fun value : ℂ => normPower (GeneralLinearGroup.det binary)
      (binaryInductionExponent degree .plane parameter) * value) scaled

theorem integral_lineLevi_normalized {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL) :
    (∫ coordinates, standardIntegrand (fun _ => function) parameter
      (lineLevi 1 binary * argument) coordinates ∂radicalMeasure) =
      normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .line parameter) *
        ∫ coordinates, cuspIntegrand data parameter function induced binary argument
          coordinates ∂radicalMeasure := by
  apply smul_right_injective ℂ
    (ne_of_gt (adeleNorm_pos (GeneralLinearGroup.det binary)))
  change (adeleNorm (GeneralLinearGroup.det binary) : ℝ) •
      (∫ coordinates, standardIntegrand (fun _ => function) parameter
        (lineLevi 1 binary * argument) coordinates ∂radicalMeasure) =
    (adeleNorm (GeneralLinearGroup.det binary) : ℝ) •
      (normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .line parameter) *
        ∫ coordinates, cuspIntegrand data parameter function induced binary argument
          coordinates ∂radicalMeasure)
  rw [integral_lineLevi data parameter function induced binary argument,
    HilbertBinaryCovariance.binaryExponent_shift, NormPower.normPower_add,
    HilbertBinaryCovariance.normPower_one_unit]
  simp only [Complex.real_smul]
  ring

theorem cuspIntegrand_integrable_of_standard {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (binary : BinaryAdelicGL) (argument : AdelicGL)
    (standardIntegrable : Integrable
      (standardIntegrand (fun _ => function) parameter (lineLevi 1 binary * argument))
        radicalMeasure) :
    Integrable (cuspIntegrand data parameter function induced binary argument)
      radicalMeasure := by
  have integrandEquality :
      (fun coordinates : Adeles × Adeles => standardIntegrand (fun _ => function) parameter
        (lineLevi 1 binary * argument) coordinates) =
      (fun coordinates => normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .plane parameter) *
        cuspIntegrand data parameter function induced binary argument
          (BinaryGaussian.rowAction binary coordinates)) := by
    funext coordinates
    exact integrand_lineLevi data parameter function induced binary argument coordinates
  change Integrable (fun coordinates => standardIntegrand (fun _ => function) parameter
    (lineLevi 1 binary * argument) coordinates) radicalMeasure at standardIntegrable
  rw [integrandEquality] at standardIntegrable
  have factorUnit : IsUnit (normPower (GeneralLinearGroup.det binary)
      (binaryInductionExponent degree .plane parameter)) :=
    isUnit_iff_ne_zero.mpr (ParabolicInvariance.normPower_ne_zero _ _)
  have composed : Integrable (fun coordinates =>
      cuspIntegrand data parameter function induced binary argument
        (BinaryGaussian.rowAction binary coordinates)) radicalMeasure :=
    (integrable_const_mul_iff factorUnit _).mp standardIntegrable
  have mapped : Integrable (cuspIntegrand data parameter function induced binary argument)
      (Measure.map (BinaryGaussian.rowAction binary) radicalMeasure) :=
    (integrable_map_equiv (BinaryGaussian.rowEquiv binary).toHomeomorph.toMeasurableEquiv
      (cuspIntegrand data parameter function induced binary argument)).mpr composed
  have scaled : Integrable (cuspIntegrand data parameter function induced binary argument)
      (adeleNorm (GeneralLinearGroup.det binary) •
        Measure.map (BinaryGaussian.rowAction binary) radicalMeasure) :=
    mapped.smul_measure ENNReal.coe_ne_top
  rw [BinaryRowMeasure.row_scale binary] at scaled
  exact scaled

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ScalarBinaryIntegral
