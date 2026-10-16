module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.CuspTheta
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.ThetaDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformVectorTheta

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem large_log {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : Set (SchwartzMap RealSpace Source)) (testsBounded : UniformSchwartzBounds.Bounded tests)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ realTest ∈ tests, realTest 0 = 0 → ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ scalarLog → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp ((power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          ‖VectorTheta.fullTheta data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation))‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := UniformCuspTheta.large data family continuous tests testsBounded finiteScale offset
    (WeightedAbsoluteTheta.finiteParameters point) (WeightedAbsoluteTheta.finiteParameters_compact point)
    (realGroup point) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun realTest testMembership zeroValue integral rotation scalarLog heightLog horizontal scalarNonnegative heightNonnegative horizontalBound => ?_⟩
  rw [norm_chart, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded realTest testMembership zeroValue (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩
      (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.one_le_exp scalarNonnegative)

theorem small_log {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : Set (SchwartzMap RealSpace Source)) (testsBounded : UniformSchwartzBounds.Bounded tests)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ realTest ∈ tests, FourierTransform.fourier realTest 0 = 0 → ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), scalarLog ≤ 0 → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp (-(power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          ‖VectorTheta.fullTheta data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation))‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := UniformCuspTheta.small data family continuous tests testsBounded finiteScale offset
    (WeightedAbsoluteTheta.finiteParameters point) (WeightedAbsoluteTheta.finiteParameters_compact point)
    (realGroup point) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun realTest testMembership zeroFourier integral rotation scalarLog heightLog horizontal scalarNonpositive heightNonnegative horizontalBound => ?_⟩
  rw [norm_chart, Real.exp_add, neg_mul, Real.exp_neg, Real.exp_nat_mul, ← inv_pow, Real.exp_nat_mul]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded realTest testMembership zeroFourier (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩
      (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr scalarNonpositive)


end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformVectorTheta
