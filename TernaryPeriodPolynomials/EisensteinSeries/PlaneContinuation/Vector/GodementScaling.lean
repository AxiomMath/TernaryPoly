module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.Godement
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.ScalingFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodement TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementRealScaling

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodementScaling

def dilate {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (scale : ℝˣ) (value : Rectangular Adeles) : data.cusp.smooth := test (value * (scalar scale).val)

theorem scalar_commute (scale : ℝˣ) (binary : BinaryAdelicGL) : scalar scale * binary = binary * scalar scale := by
  unfold GodementRealScaling.scalar
  rw [CohomologicalCenter.atInfinity_scalar, GeneralLinearGroup.scalar_commute]

theorem integrand_dilate {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (scale : ℝˣ) (positive : 0 < scale.val) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    integrand data (dilate data test scale) parameter point binary =
      multiplier data scale parameter * integrand data test parameter point (scalar scale * binary) := by
  have argument : frame point * (scalar scale * binary).val = (frame point * binary.val) * (scalar scale).val := by
    rw [scalar_commute, Units.val_mul, Matrix.mul_assoc]
  unfold integrand
  rw [argument, cusp_scalar data _ scale positive, map_mul, map_mul]
  unfold dilate multiplier
  have nonzero := character_ne_zero (innerCharacter data parameter) (GeneralLinearGroup.det (scalar scale))
  field_simp

theorem integrable_dilate {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (scale : ℝˣ) (positive : 0 < scale.val) (parameter : ℂ) (point : AdelicGL)
    (integrable : Integrable (integrand data test parameter point) BinaryHaar.measure) :
    Integrable (integrand data (dilate data test scale) parameter point) BinaryHaar.measure := by
  change Integrable (fun binary => integrand data (dilate data test scale) parameter point binary) _
  simpa only [integrand_dilate data test scale positive] using
    (integrable.comp_mul_left (scalar scale)).const_mul (multiplier data scale parameter)

theorem section_dilate {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (scale : ℝˣ) (positive : 0 < scale.val) (parameter : ℂ) (point : AdelicGL) :
    VectorGodement.sectionFunction data (dilate data test scale) parameter point =
      multiplier data scale parameter * VectorGodement.sectionFunction data test parameter point := by
  simp only [VectorGodement.sectionFunction, integrand_dilate data test scale positive,
    integral_const_mul, integral_mul_left_eq_self]
  ring

theorem integrand_sub_smul {degree : ℕ} (data : InducingData degree)
    (first second : Rectangular Adeles → data.cusp.smooth) (coefficient : ℂ)
    (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    integrand data (fun value => first value - coefficient • second value) parameter point binary =
      integrand data first parameter point binary - coefficient * integrand data second parameter point binary := by
  simp only [integrand, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem section_sub_smul {degree : ℕ} (data : InducingData degree)
    (first second : Rectangular Adeles → data.cusp.smooth) (coefficient : ℂ)
    (parameter : ℂ) (point : AdelicGL)
    (firstIntegrable : Integrable (integrand data first parameter point) BinaryHaar.measure)
    (secondIntegrable : Integrable (integrand data second parameter point) BinaryHaar.measure) :
    VectorGodement.sectionFunction data (fun value => first value - coefficient • second value) parameter point =
      VectorGodement.sectionFunction data first parameter point - coefficient * VectorGodement.sectionFunction data second parameter point := by
  simp only [VectorGodement.sectionFunction, integrand_sub_smul,
    integral_sub firstIntegrable (secondIntegrable.const_mul coefficient), integral_const_mul]
  ring

def regularize {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth) :
    Rectangular Adeles → data.cusp.smooth :=
  let first := fun value => test value - dilate data test SchwartzRegularization.scale value
  fun value => first value - (64 : ℂ) • dilate data first SchwartzRegularization.scale value

theorem section_regularize {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL)
    (integrable : Integrable (integrand data test parameter point) BinaryHaar.measure) :
    VectorGodement.sectionFunction data (regularize data test) parameter point =
      GodementScalingFactor.regularizationFactor data parameter * VectorGodement.sectionFunction data test parameter point := by
  let first := fun value => test value - (1 : ℂ) • dilate data test SchwartzRegularization.scale value
  have dilateIntegrable := integrable_dilate data test SchwartzRegularization.scale SchwartzRegularization.scale_pos parameter point integrable
  have firstIntegrable : Integrable (integrand data first parameter point) BinaryHaar.measure := by
    have functionEquality : integrand data first parameter point =
        integrand data test parameter point -
          (fun binary => (1 : ℂ) * integrand data (dilate data test SchwartzRegularization.scale) parameter point binary) := by
      funext binary
      exact integrand_sub_smul data test _ 1 parameter point binary
    rw [functionEquality]
    exact integrable.sub (dilateIntegrable.const_mul (1 : ℂ))
  have firstDilateIntegrable := integrable_dilate data first SchwartzRegularization.scale SchwartzRegularization.scale_pos parameter point firstIntegrable
  have equality : regularize data test = fun value => first value - (64 : ℂ) • dilate data first SchwartzRegularization.scale value := by
    simp only [regularize, first, one_smul]
  rw [equality, section_sub_smul data first _ _ parameter point firstIntegrable firstDilateIntegrable,
    section_dilate data first SchwartzRegularization.scale SchwartzRegularization.scale_pos]
  dsimp only [first]
  rw [section_sub_smul data test _ _ parameter point integrable dilateIntegrable,
    section_dilate data test SchwartzRegularization.scale SchwartzRegularization.scale_pos]
  unfold GodementScalingFactor.regularizationFactor
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodementScaling
