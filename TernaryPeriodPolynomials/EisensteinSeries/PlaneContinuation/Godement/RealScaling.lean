module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ZeroConstantThetaIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementRealScaling

def scalar (scale : ℝˣ) : BinaryAdelicGL := atInfinity (GeneralLinearGroup.scalar (Fin 2) scale)

theorem scalar_inv (scale : ℝˣ) : scalar scale⁻¹ = (scalar scale)⁻¹ := by
  rw [scalar, scalar, CohomologicalCenter.atInfinity_scalar, CohomologicalCenter.atInfinity_scalar, ← map_inv]
  congr 1

theorem matrixTerm_dilate (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (scale : ℝˣ) (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) :
    matrixTerm (AdelicSchwartzTheta.tensorTest (RealFourierScaling.dilate realTest scale) finiteTest) point binary matrix =
      matrixTerm (AdelicSchwartzTheta.tensorTest realTest finiteTest) point (scalar scale * binary) matrix := by
  simp only [AdelicSchwartzTheta.matrixTerm_factorization, AdelicSchwartzTheta.realPullback,
    AdelicSchwartzTheta.finitePullback, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    RealFourierScaling.dilate_apply, scalar, map_mul, SiegelChartFunctions.real_projection_infinite,
    SiegelChartFunctions.finite_projection_infinite, one_mul, SiegelChartFunctions.realTransform_scalar]

theorem kernel_dilate (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (scale : ℝˣ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    kernel (AdelicSchwartzTheta.tensorTest (RealFourierScaling.dilate realTest scale) finiteTest) point binary =
      kernel (AdelicSchwartzTheta.tensorTest realTest finiteTest) point (scalar scale * binary) := by
  have equality := matrixTerm_dilate realTest finiteTest scale point binary (standard : Rectangular ℚ)
  simpa only [matrixTerm, standard_map, kernel] using equality

theorem cusp_scalar {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (scale : ℝˣ) (positive : 0 < scale.val) (binary : BinaryAdelicGL) :
    data.cusp.realize vector (scalar scale * binary) = data.cusp.realize vector binary := by
  rw [scalar, CohomologicalCenter.atInfinity_scalar, data.cusp.central,
    CohomologicalCenter.centralCharacter_positiveReal data scale positive, one_mul]

def multiplier {degree : ℕ} (data : InducingData degree) (scale : ℝˣ) (parameter : ℂ) : ℂ :=
  (innerCharacter data parameter (GeneralLinearGroup.det (scalar scale)))⁻¹

theorem raw_dilate {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (scale : ℝˣ) (positive : 0 < scale.val) (parameter : ℂ) (point : AdelicGL) :
    raw (AdelicSchwartzTheta.tensorTest (RealFourierScaling.dilate realTest scale) finiteTest) (innerCharacter data parameter) data.cusp vector point =
      multiplier data scale parameter * raw (AdelicSchwartzTheta.tensorTest realTest finiteTest) (innerCharacter data parameter) data.cusp vector point := by
  have cuspInverse (binary : BinaryAdelicGL) : data.cusp.realize vector ((scalar scale)⁻¹ * binary) = data.cusp.realize vector binary := by
    rw [← scalar_inv]
    exact cusp_scalar data vector scale⁻¹ (by simpa only [Units.val_inv_eq_inv_val] using inv_pos.mpr positive) binary
  unfold raw
  rw [← integral_mul_left_eq_self (fun binary =>
    kernel (AdelicSchwartzTheta.tensorTest (RealFourierScaling.dilate realTest scale) finiteTest) point binary *
      innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary) (scalar scale)⁻¹]
  simp only [kernel_dilate, mul_inv_cancel_left, map_mul, map_inv, cuspInverse]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => by dsimp only [multiplier]; ring)

theorem section_dilate {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (scale : ℝˣ) (positive : 0 < scale.val) (parameter : ℂ) (point : AdelicGL) :
    sectionFunction data (AdelicSchwartzTheta.tensorTest (RealFourierScaling.dilate realTest scale) finiteTest) vector parameter point =
      multiplier data scale parameter * sectionFunction data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point := by
  simp only [sectionFunction, raw_dilate data vector realTest finiteTest scale positive]
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementRealScaling
