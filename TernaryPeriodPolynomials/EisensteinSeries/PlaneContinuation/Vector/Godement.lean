module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FrameProfile

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodement

def integrand {degree : ℕ} (data : InducingData degree)
    (test : Rectangular Adeles → data.cusp.smooth) (parameter : ℂ)
    (point : AdelicGL) (binary : BinaryAdelicGL) : ℂ :=
  innerCharacter data parameter (GeneralLinearGroup.det binary) *
    data.cusp.realize (test (frame point * binary.val)) binary

def sectionFunction {degree : ℕ} (data : InducingData degree)
    (test : Rectangular Adeles → data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) : ℂ :=
  outerCharacter data parameter (GeneralLinearGroup.det point) *
    ∫ binary, integrand data test parameter point binary ∂BinaryHaar.measure

theorem scalar_test {degree : ℕ} (data : InducingData degree)
    (test : Rectangular Adeles → ℂ) (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) :
    sectionFunction data (fun value => test value • vector) parameter point =
      GodementIntegral.sectionFunction data test vector parameter point := by
  unfold sectionFunction GodementIntegral.sectionFunction GodementIntegral.raw
  congr 1
  apply integral_congr_ae
  filter_upwards [] with binary
  simp only [integrand, map_smul, Pi.smul_apply, smul_eq_mul, frame, kernel]
  ring

def recoveryTest {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular Adeles → ℂ) (value : Rectangular Adeles) : data.cusp.smooth :=
  cutoff value • profile induced value

theorem recovery_integrand {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    integrand data (recoveryTest induced cutoff) parameter point binary =
      cutoff (frame point * binary.val) *
        ((outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ * function point) := by
  simp only [integrand, recoveryTest, map_smul, Pi.smul_apply, smul_eq_mul,
    realize_profile_frame_mul, mul_inv_cancel, normalized]
  simp only [← induced_eq_planeCuspVector_one induced]
  have nonzero := character_ne_zero (innerCharacter data parameter) (GeneralLinearGroup.det binary)
  field_simp

theorem recovery_integrable {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular Adeles → ℂ) (point : AdelicGL)
    (cutoffIntegrable : Integrable (fun binary : BinaryAdelicGL => cutoff (frame point * binary.val)) BinaryHaar.measure) :
    Integrable (integrand data (recoveryTest induced cutoff) parameter point) BinaryHaar.measure := by
  change Integrable (fun binary => integrand data (recoveryTest induced cutoff) parameter point binary) _
  simpa only [recovery_integrand] using cutoffIntegrable.mul_const
    ((outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ * function point)

theorem recovery_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular Adeles → ℂ) (point : AdelicGL) :
    sectionFunction data (recoveryTest induced cutoff) parameter point =
      (∫ binary : BinaryAdelicGL, cutoff (frame point * binary.val) ∂BinaryHaar.measure) * function point := by
  simp only [sectionFunction, recovery_integrand, integral_mul_const]
  have nonzero := character_ne_zero (outerCharacter data parameter) (GeneralLinearGroup.det point)
  field_simp

theorem recovery_of_mass_one {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular Adeles → ℂ)
    (mass : ∀ point : AdelicGL,
      (∫ binary : BinaryAdelicGL, cutoff (frame point * binary.val) ∂BinaryHaar.measure) = 1) :
    sectionFunction data (recoveryTest induced cutoff) parameter = function := by
  funext point
  rw [recovery_eq, mass, one_mul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodement
