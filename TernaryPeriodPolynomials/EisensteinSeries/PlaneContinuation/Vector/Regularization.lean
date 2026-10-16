module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.Unfolding
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.GodementScaling

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorRegularization

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem finite_dilate (scale : ℝˣ) (matrix : Rectangular Adeles) :
    finite (matrix * (GodementRealScaling.scalar scale).val) = finite matrix := by
  unfold finite
  rw [Matrix.map_mul]
  change matrix.map (RingHom.snd ℝ FiniteAdeles) *
    (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (GodementRealScaling.scalar scale)).val = _
  rw [GodementRealScaling.scalar, SiegelChartFunctions.finite_projection_infinite, Units.val_one, Matrix.mul_one]

theorem archimedean_dilate (scale : ℝˣ) (matrix : Rectangular Adeles) :
    archimedean (matrix * (GodementRealScaling.scalar scale).val) = scale.val • archimedean matrix := by
  unfold archimedean
  rw [Matrix.map_mul]
  change coordinateEquiv (matrix.map (RingHom.fst ℝ FiniteAdeles) *
    (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (GodementRealScaling.scalar scale)).val) = _
  rw [GodementRealScaling.scalar, SiegelChartFunctions.real_projection_infinite, ← coordinateEquiv.map_smul]
  congr 1
  change matrix.map (RingHom.fst ℝ FiniteAdeles) * Matrix.diagonal (fun _ => scale.val) =
    scale.val • matrix.map (RingHom.fst ℝ FiniteAdeles)
  ext row column
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]

omit [CompleteSpace Source] in
theorem lift_dilate {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ) (scale : ℝˣ) :
    liftTest data family (BanachAdelicTheta.tensorTest (BanachSchwartzRegularization.dilate realTest scale) finiteTest) =
      VectorGodementScaling.dilate data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) scale := by
  funext matrix
  simp only [liftTest, BanachAdelicTheta.tensorTest, BanachSchwartzRegularization.dilate_apply,
    VectorGodementScaling.dilate, finite_dilate, archimedean_dilate]

omit [CompleteSpace Source] in
theorem lift_sub_smul {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (first second : SchwartzMap RealSpace Source) (coefficient : ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ) :
    liftTest data family (BanachAdelicTheta.tensorTest (first - coefficient • second) finiteTest) =
      fun matrix => liftTest data family (BanachAdelicTheta.tensorTest first finiteTest) matrix -
        coefficient • liftTest data family (BanachAdelicTheta.tensorTest second finiteTest) matrix := by
  funext matrix
  simp only [liftTest, BanachAdelicTheta.tensorTest, _root_.sub_apply, _root_.smul_apply,
    smul_sub, smul_comm _ coefficient, map_sub, map_smul]
  rfl

omit [CompleteSpace Source] in
theorem lift_regularize {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ) :
    liftTest data family (BanachAdelicTheta.tensorTest (BanachSchwartzRegularization.regularize realTest) finiteTest) =
      VectorGodementScaling.regularize data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) := by
  have first : liftTest data family (BanachAdelicTheta.tensorTest (BanachSchwartzRegularization.killValue realTest) finiteTest) =
      fun matrix => liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest) matrix -
        VectorGodementScaling.dilate data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) SchwartzRegularization.scale matrix := by
    have result := lift_sub_smul data family realTest (BanachSchwartzRegularization.dilate realTest SchwartzRegularization.scale) 1 finiteTest
    simpa only [BanachSchwartzRegularization.killValue, one_smul, lift_dilate] using result
  rw [BanachSchwartzRegularization.regularize, BanachSchwartzRegularization.killFourier,
    lift_sub_smul, lift_dilate, first]
  rfl

theorem section_regularize {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    VectorGodement.sectionFunction data (liftTest data family
      (BanachAdelicTheta.tensorTest (BanachSchwartzRegularization.regularize realTest) finiteTest)) parameter point =
      GodementScalingFactor.regularizationFactor data parameter *
        VectorGodement.sectionFunction data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest)) parameter point := by
  rw [lift_regularize]
  exact VectorGodementScaling.section_regularize data _ parameter point
    (VectorUnfolding.raw_integrable_at data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorRegularization
