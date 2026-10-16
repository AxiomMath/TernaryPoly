module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.Godement
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CuspidalSectionRelations

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodementRelations

theorem frame_unipotent (point : AdelicGL) (first second : Adeles) :
    frame (planeUnipotent first second * point) = frame point := by
  have standardFixed : (planeUnipotent first second)⁻¹.val * standard = standard := by
    rw [standard, mul_standard]
    apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;> simp [columns, planeUnipotent, Matrix.one_apply]
  unfold frame
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, standardFixed]

theorem frame_levi_mul (point : AdelicGL) (binary left : BinaryAdelicGL) (scalar : Adelesˣ) :
    frame (planeLevi left scalar * point) * binary.val = frame point * (left⁻¹ * binary).val := by
  have inverseStandard : (planeLevi left scalar)⁻¹.val * standard = standard * left⁻¹.val := by
    rw [standard, mul_standard]
    apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;>
      simp [columns, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  unfold frame
  rw [_root_.mul_inv_rev, Units.val_mul,
    Matrix.mul_assoc point⁻¹.val (planeLevi left scalar)⁻¹.val standard, inverseStandard, Units.val_mul]
  simp only [Matrix.mul_assoc]

def orbit {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (left : BinaryAdelicGL) : ℂ :=
  ∫ binary, innerCharacter data parameter (GeneralLinearGroup.det binary) *
    data.cusp.realize (test (frame point * binary.val)) (left * binary) ∂BinaryHaar.measure

theorem section_unipotent {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (first second : Adeles) :
    VectorGodement.sectionFunction data test parameter (planeUnipotent first second * point) =
      VectorGodement.sectionFunction data test parameter point := by
  simp only [VectorGodement.sectionFunction, VectorGodement.integrand, frame_unipotent,
    map_mul, det_planeUnipotent, one_mul]

theorem raw_levi {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (left : BinaryAdelicGL) (scalar : Adelesˣ) :
    (∫ binary, VectorGodement.integrand data test parameter (planeLevi left scalar * point) binary ∂BinaryHaar.measure) =
      innerCharacter data parameter (GeneralLinearGroup.det left) * orbit data test parameter point left := by
  rw [← integral_mul_left_eq_self (VectorGodement.integrand data test parameter (planeLevi left scalar * point)) left]
  simp only [VectorGodement.integrand, frame_levi_mul, inv_mul_cancel_left, map_mul]
  rw [orbit, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => mul_assoc _ _ _)

theorem section_levi {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (left : BinaryAdelicGL) (scalar : Adelesˣ) :
    VectorGodement.sectionFunction data test parameter (planeLevi left scalar * point) =
      outerCharacter data parameter scalar * normPower (GeneralLinearGroup.det left) (binaryInductionExponent degree .plane parameter) *
        (outerCharacter data parameter (GeneralLinearGroup.det point) * orbit data test parameter point left) := by
  rw [VectorGodement.sectionFunction, raw_levi, map_mul, det_planeLevi, map_mul, map_mul]
  have cancellation := characters_product data parameter (GeneralLinearGroup.det left)
  calc
    _ = outerCharacter data parameter scalar *
        (outerCharacter data parameter (GeneralLinearGroup.det left) * innerCharacter data parameter (GeneralLinearGroup.det left)) *
        (outerCharacter data parameter (GeneralLinearGroup.det point) * orbit data test parameter point left) := by ring
    _ = _ := by rw [cancellation]

theorem orbit_rational {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (rational : BinaryRationalGL) :
    orbit data test parameter point (GeneralLinearGroup.map rationalAdele rational) =
      ∫ binary, VectorGodement.integrand data test parameter point binary ∂BinaryHaar.measure := by
  simp only [orbit, VectorGodement.integrand, data.cusp.leftRational]

theorem section_rational_plane {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (element : planeParabolic ℚ) :
    VectorGodement.sectionFunction data test parameter (rationalGroup element.val * point) =
      VectorGodement.sectionFunction data test parameter point := by
  let adelic := RationalInvariance.rationalPlane element
  have factorization := planeParabolic_factorization adelic
  change VectorGodement.sectionFunction data test parameter (adelic.val * point) = _
  rw [factorization, mul_assoc, section_unipotent, section_levi]
  change outerCharacter data parameter (planeCornerUnit (RationalInvariance.rationalPlane element)) *
    normPower (GeneralLinearGroup.det (planeBinaryBlock (RationalInvariance.rationalPlane element)))
      (binaryInductionExponent degree .plane parameter) *
    (outerCharacter data parameter (GeneralLinearGroup.det point) *
      orbit data test parameter point (planeBinaryBlock (RationalInvariance.rationalPlane element))) = _
  have binaryNorm : normPower (GeneralLinearGroup.det (planeBinaryBlock (RationalInvariance.rationalPlane element)))
      (binaryInductionExponent degree .plane parameter) = 1 := by
    rw [RationalInvariance.binaryBlock_rational, GeneralLinearGroup.map_det]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula.normPower_rational _ _
  have outerRational : outerCharacter data parameter (planeCornerUnit (RationalInvariance.rationalPlane element)) = 1 := by
    change data.chi.toMonoidHom (planeCornerUnit (RationalInvariance.rationalPlane element)) *
      normPower (planeCornerUnit (RationalInvariance.rationalPlane element)) (-2 * inductionExponent .plane parameter) = 1
    have character : data.chi.toMonoidHom (planeCornerUnit (RationalInvariance.rationalPlane element)) = 1 := by
      rw [RationalInvariance.corner_rational]
      exact data.chi.rational _
    have norm : normPower (planeCornerUnit (RationalInvariance.rationalPlane element))
        (-2 * inductionExponent .plane parameter) = 1 := by
      rw [RationalInvariance.corner_rational]
      exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula.normPower_rational _ _
    rw [character, norm, mul_one]
  rw [binaryNorm, outerRational, one_mul, one_mul, RationalInvariance.binaryBlock_rational, orbit_rational]
  rfl

def cuspKernel {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (pair : Adeles × BinaryAdelicGL) : ℂ :=
  innerCharacter data parameter (GeneralLinearGroup.det pair.2) *
    data.cusp.realize (test (frame point * pair.2.val)) (binaryUnipotent pair.1 * pair.2)

theorem section_binary_unipotent {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL) (value : Adeles) :
    VectorGodement.sectionFunction data test parameter (planeLevi (binaryUnipotent value) 1 * point) =
      outerCharacter data parameter (GeneralLinearGroup.det point) * orbit data test parameter point (binaryUnipotent value) := by
  rw [section_levi, TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneUnipotentCharts.binaryUnipotent_det, map_one, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_one,
    one_mul, one_mul]

theorem cuspidal {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ) (point : AdelicGL)
    (integrable : Integrable (cuspKernel data test parameter point)
      ((adeleMeasure.restrict additiveDomain).prod BinaryHaar.measure)) :
    (∫ value in additiveDomain,
      VectorGodement.sectionFunction data test parameter (planeLevi (binaryUnipotent value) 1 * point) ∂adeleMeasure) = 0 := by
  simp only [section_binary_unipotent, integral_const_mul]
  have meanZero (binary : BinaryAdelicGL) :
      (∫ value in additiveDomain, innerCharacter data parameter (GeneralLinearGroup.det binary) *
        data.cusp.realize (test (frame point * binary.val)) (binaryUnipotent value * binary) ∂adeleMeasure) = 0 := by
    rw [integral_const_mul, (data.cusp.cuspidal (test (frame point * binary.val)) binary).2, mul_zero]
  have equality : (∫ value in additiveDomain, orbit data test parameter point (binaryUnipotent value) ∂adeleMeasure) = 0 := by
    have productIntegrable : Integrable (Function.uncurry (fun value binary =>
        innerCharacter data parameter (GeneralLinearGroup.det binary) *
          data.cusp.realize (test (frame point * binary.val)) (binaryUnipotent value * binary)))
        ((adeleMeasure.restrict additiveDomain).prod BinaryHaar.measure) := integrable
    unfold orbit
    rw [integral_integral_swap productIntegrable]
    simp only [meanZero, integral_zero]
  rw [equality, mul_zero]

theorem relations {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → data.cusp.smooth)
    (parameter : ℂ)
    (integrable : ∀ point, Integrable (cuspKernel data test parameter point)
      ((adeleMeasure.restrict additiveDomain).prod BinaryHaar.measure)) :
    CuspidalSectionRelations.Relations (VectorGodement.sectionFunction data test parameter) :=
  ⟨fun element point => section_rational_plane data test parameter point element,
    fun first second point => section_unipotent data test parameter point first second,
    fun point => cuspidal data test parameter point (integrable point)⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodementRelations
