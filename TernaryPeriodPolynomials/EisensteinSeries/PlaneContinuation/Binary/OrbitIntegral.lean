module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.OrbitTestFamilies

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryProductHaar TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealBinaryRecovery TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitIntegral

def smoothProfile {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (parameter : ℂ) (frame : Rectangular ℝ) : data.cusp.smooth :=
  BinaryOrbitProfile.coefficient degree parameter frame •
    smoothTranslate data.cusp (invertibleMatrix (BinaryOrbitChart.block frame)⁻¹) vector

theorem smoothProfile_val {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (parameter : ℂ) (frame : Rectangular ℝ) :
    (smoothProfile data vector parameter frame).val = BinaryOrbitProfile.profile data vector parameter frame := rfl

theorem smoothProfile_standard {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (parameter : ℂ) (binary : BinaryRealGL) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (smoothProfile data vector parameter (columns (1 : PlaneMatrix) * binary.val))
      (evaluation * atInfinity binary) =
        BinaryOrbitProfile.coefficient degree parameter (columns (1 : PlaneMatrix) * binary.val) *
          data.cusp.realize vector evaluation := by
  simp only [smoothProfile, map_smul, Pi.smul_apply, smul_eq_mul,
    BinaryOrbitChart.block_mul, BinaryOrbitChart.block_standard, one_mul]
  rw [← GeneralLinearGroup.coe_inv, invertibleMatrix_units, smoothTranslate_realize,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_inv, mul_inv_cancel_right]

def test {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (cutoff : Rectangular ℝ → ℝ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (parameter : ℂ) (value : Rectangular Adeles) : data.cusp.smooth :=
  finiteTest (finite value) • (cutoff (coordinateEquiv.symm (archimedean value)) •
    smoothProfile data vector parameter (coordinateEquiv.symm (archimedean value)))

theorem liftTest_eq {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    {Index : Type} [Fintype Index] (radii : Index → ℝ≥0) (positive : ∀ index, 0 < radii index)
    (cutoff : Rectangular ℝ → ℝ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (parameter : ℂ) (realTest : SchwartzMap RealSpace (ProductStages.Source data.cusp radii positive))
    (image : ∀ value, (ProductStages.smoothMap data.cusp radii positive (realTest value)).val.val =
      cutoff (coordinateEquiv.symm value) • BinaryOrbitProfile.profile data vector parameter (coordinateEquiv.symm value)) :
    VectorMatrixOrbit.liftTest data (ProductStages.smoothMap data.cusp radii positive)
      (BanachAdelicTheta.tensorTest realTest finiteTest) = test data vector cutoff finiteTest parameter := by
  funext value
  apply Subtype.ext
  change (ProductStages.smoothMap data.cusp radii positive
    (finiteTest (finite value) • realTest (archimedean value))).val.val = _
  rw [map_smul]
  change finiteTest (finite value) • (ProductStages.smoothMap data.cusp radii positive
    (realTest (archimedean value))).val.val = _
  rw [image]
  rfl

theorem realFrame_atFinite (point : FiniteGL) : realFrame (atFinite point) = columns (1 : PlaneMatrix) := by
  change columns (1 : RealGL3)⁻¹.val = _
  rw [inv_one, Units.val_one]

def kernel {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (parameter : ℂ) (point : FiniteGL)
    (binary : BinaryFiniteGL) : ℂ :=
  finiteTest (finite (FrameProfile.frame (atFinite point) * (atFinite binary).val)) *
    innerCharacter data parameter (GeneralLinearGroup.det (atFinite binary)) * data.cusp.realize vector (atFinite binary)

theorem integrand_separated {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (cutoff : Rectangular ℝ → ℝ) (supported : tsupport cutoff ⊆ BinaryOrbitChart.domain)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (parameter : ℂ) (point : FiniteGL)
    (finiteBinary : BinaryFiniteGL) (realBinary : BinaryRealGL) :
    VectorGodement.integrand data (test data vector cutoff finiteTest parameter) parameter (atFinite point)
      (atFinite finiteBinary * atInfinity realBinary) =
        (cutoff (columns (1 : PlaneMatrix) * realBinary.val) : ℂ) * kernel data vector finiteTest parameter point finiteBinary := by
  simp only [VectorGodement.integrand, test, Units.val_mul, ← Matrix.mul_assoc,
    finite_mul_infinity, real_mul_infinity, real_mul_finite, ← realFrame_eq,
    realFrame_atFinite, map_smul, LinearMap.map_smul_of_tower, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
    map_mul, smoothProfile_standard, kernel]
  by_cases zero : cutoff (columns (1 : PlaneMatrix) * realBinary.val) = 0
  · simp only [zero, Complex.ofReal_zero, zero_mul, mul_zero]
  · have inside := supported (subset_tsupport _ zero)
    have positive : 0 < realBinary.val.det := by
      simpa only [BinaryOrbitChart.domain, Set.mem_ofPred_eq, BinaryOrbitChart.block_mul,
        BinaryOrbitChart.block_standard, one_mul] using inside
    have cancel := BinaryOrbitProfile.coefficient_inner data parameter realBinary positive
    calc
      _ = (cutoff (columns (1 : PlaneMatrix) * realBinary.val) : ℂ) *
          (finiteTest (finite (FrameProfile.frame (atFinite point) * (atFinite finiteBinary).val)) *
            innerCharacter data parameter (GeneralLinearGroup.det (atFinite finiteBinary)) * data.cusp.realize vector (atFinite finiteBinary)) *
          (BinaryOrbitProfile.coefficient degree parameter (columns (1 : PlaneMatrix) * realBinary.val) *
            innerCharacter data parameter (GeneralLinearGroup.det (atInfinity realBinary))) := by ring
      _ = _ := by rw [cancel, mul_one]

def coefficientIntegral {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (parameter : ℂ) (point : FiniteGL) : ℂ :=
  ∫ binary, kernel data vector finiteTest parameter point binary ∂BinaryProductHaar.finiteMeasure

theorem section_eq {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (cutoff : Rectangular ℝ → ℝ) (supported : tsupport cutoff ⊆ BinaryOrbitChart.domain)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (parameter : ℂ) (point : FiniteGL) :
    VectorGodement.sectionFunction data (test data vector cutoff finiteTest parameter) parameter (atFinite point) =
      RealOrbitalMass.mass cutoff 1 * outerCharacter data parameter (GeneralLinearGroup.det (atFinite point)) *
        coefficientIntegral data vector finiteTest parameter point := by
  rw [VectorGodement.sectionFunction, integral_product]
  simp_rw [integrand_separated data vector cutoff supported finiteTest parameter point]
  rw [integral_prod_mul (fun binary : BinaryRealGL => (cutoff (columns (1 : PlaneMatrix) * binary.val) : ℂ))
    (kernel data vector finiteTest parameter point)]
  have identityFrame : realFrame 1 = columns (1 : PlaneMatrix) := by
    rw [realFrame, map_one, inv_one, Units.val_one]
  unfold RealOrbitalMass.mass coefficientIntegral
  rw [identityFrame]
  ring

theorem exists_cutoff :
    ∃ cutoff : Rectangular ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff ∧ HasCompactSupport cutoff ∧
      tsupport cutoff ⊆ BinaryOrbitChart.domain ∧ RealOrbitalMass.mass cutoff 1 ≠ 0 := by
  obtain ⟨cutoff, smooth, compact, supported, range, value⟩ := BinaryOrbitChart.exists_cutoff
  refine ⟨cutoff, smooth, compact, supported, ?_⟩
  apply RealOrbitalMass.nonzero cutoff smooth.continuous compact (supported.trans BinaryOrbitChart.domain_fullRank)
    (fun point => (range ⟨point, rfl⟩).1) 1
  have identityFrame : realFrame 1 = columns (1 : PlaneMatrix) := by
    rw [realFrame, map_one, inv_one, Units.val_one]
  rw [identityFrame, value]
  exact one_ne_zero

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitIntegral
