module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegralFrameOrbit

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PrimitiveFrameRecovery

def scalarCutoff (cutoff : Rectangular ℝ → ℝ) (value : Rectangular Adeles) : ℂ :=
  cutoff (coordinateEquiv.symm (archimedean value))

def mass (cutoff : Rectangular ℝ → ℝ) (point : AdelicGL) : ℂ :=
  ∫ binary in integralRegion, scalarCutoff cutoff (FrameProfile.frame point * binary.val) ∂BinaryHaar.measure

def remainder {degree : ℕ} (data : InducingData degree)
    (test : Rectangular Adeles → data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) : ℂ :=
  outerCharacter data parameter (GeneralLinearGroup.det point) *
    ∫ binary in integralRegionᶜ, VectorGodement.integrand data test parameter point binary ∂BinaryHaar.measure

theorem test_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (test : Rectangular Adeles → data.cusp.smooth)
    (cutoff : Rectangular ℝ → ℝ)
    (interpolation : ∀ (finitePoint : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
      test (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value) =
        cutoff value • profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value))
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : BinaryAdelicGL) (binaryIntegral : binary ∈ integralRegion) :
    test (FrameProfile.frame point * binary.val) =
      VectorGodement.recoveryTest induced (scalarCutoff cutoff) (FrameProfile.frame point * binary.val) := by
  obtain ⟨finitePoint, equality⟩ := orbit_integral point pointIntegral binary binaryIntegral
  rw [equality, interpolation finitePoint _ (realFrame_fullRank _)]
  simp only [VectorGodement.recoveryTest, scalarCutoff,
    FlatProfileInterpolation.archimedean_adelicFrame, LinearEquiv.symm_apply_apply, Complex.coe_smul]

theorem integrand_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (test : Rectangular Adeles → data.cusp.smooth)
    (cutoff : Rectangular ℝ → ℝ)
    (interpolation : ∀ (finitePoint : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
      test (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value) =
        cutoff value • profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value))
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : BinaryAdelicGL) (binaryIntegral : binary ∈ integralRegion) :
    VectorGodement.integrand data test parameter point binary =
      scalarCutoff cutoff (FrameProfile.frame point * binary.val) *
        ((outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ * function point) := by
  rw [← VectorGodement.recovery_integrand induced (scalarCutoff cutoff)]
  unfold VectorGodement.integrand
  rw [test_eq induced test cutoff interpolation point pointIntegral binary binaryIntegral]

theorem integral_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (test : Rectangular Adeles → data.cusp.smooth)
    (cutoff : Rectangular ℝ → ℝ)
    (interpolation : ∀ (finitePoint : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
      test (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value) =
        cutoff value • profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value))
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    (∫ binary in integralRegion, VectorGodement.integrand data test parameter point binary ∂BinaryHaar.measure) =
      mass cutoff point * ((outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ * function point) := by
  rw [setIntegral_congr_fun integralRegion_measurable
    (fun binary membership => integrand_eq induced test cutoff interpolation point pointIntegral binary membership)]
  exact integral_mul_const _ _

theorem section_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (test : Rectangular Adeles → data.cusp.smooth)
    (cutoff : Rectangular ℝ → ℝ)
    (interpolation : ∀ (finitePoint : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
      test (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value) =
        cutoff value • profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value))
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (integrable : Integrable (VectorGodement.integrand data test parameter point) BinaryHaar.measure) :
    VectorGodement.sectionFunction data test parameter point =
      mass cutoff point * function point + remainder data test parameter point := by
  rw [VectorGodement.sectionFunction, ← integral_add_compl integralRegion_measurable integrable,
    integral_eq induced test cutoff interpolation point pointIntegral, mul_add]
  unfold remainder
  congr 1
  have nonzero := FrameProfile.character_ne_zero (outerCharacter data parameter) (GeneralLinearGroup.det point)
  field_simp

theorem exists_decomposition {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ test : ℂ → Rectangular Adeles → data.cusp.smooth, ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter point => VectorGodement.sectionFunction data (test parameter) parameter point) continuation ∧
      ∀ (parameter : ℂ) (point : AdelicGL), (1 - (degree : ℝ)) / 2 < parameter.re →
        finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding) →
          VectorGodement.sectionFunction data (test parameter) parameter point =
            mass cutoff point * sectionFunction parameter point + remainder data (test parameter) parameter point := by
  obtain ⟨test, continuation, continues, integrable, interpolation⟩ :=
    FlatProfileInterpolation.exists_integrable_interpolation flat cutoff smooth compact supported
  refine ⟨test, continuation, continues, ?_⟩
  intro parameter point halfPlane pointIntegral
  exact section_eq (flat.1 parameter) (test parameter) cutoff (interpolation parameter)
    point pointIntegral (integrable parameter point halfPlane)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PrimitiveFrameRecovery
