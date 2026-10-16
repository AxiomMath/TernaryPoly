module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.PointCuspTheta
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.Continuity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.ThetaDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactVectorTheta

def finiteParameters (points : Set AdelicGL) : Set FiniteParameterThetaDecay.Parameter :=
  (finiteGroup '' points) ×ˢ Set.range (GeneralLinearGroup.map integralEmbedding (n := Fin 2))

theorem finiteParameters_compact (points : Set AdelicGL) (compact : IsCompact points) :
    IsCompact (finiteParameters points) := by
  let _ : CompactSpace (Matrix (Fin 2) (Fin 2) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → IntegralAdeles))
  exact (compact.image TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedContinuity.finiteGroup_continuous).prod
    (isCompact_range (TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.integralMap_continuous (size := 2)))

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem large_log {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : Set (SchwartzMap RealSpace Source)) (testsBounded : UniformSchwartzBounds.Bounded tests)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (points : Set AdelicGL) (compact : IsCompact points) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ realTest ∈ tests, realTest 0 = 0 → ∀ point ∈ points, ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ scalarLog → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp ((power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          ‖VectorTheta.fullTheta data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation))‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := CompactPointCuspTheta.large data family continuous tests testsBounded finiteScale offset
    (finiteParameters points) (finiteParameters_compact points compact)
    (realGroup '' points) (compact.image TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedContinuity.realGroup_continuous) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun realTest testMembership zeroValue point pointMembership integral rotation scalarLog heightLog horizontal scalarNonnegative heightNonnegative horizontalBound => ?_⟩
  rw [norm_chart, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded realTest testMembership zeroValue (realGroup point) ⟨point, pointMembership, rfl⟩ (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨⟨point, pointMembership, rfl⟩, ⟨integral, rfl⟩⟩
      (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.one_le_exp scalarNonnegative)

theorem small_log {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : Set (SchwartzMap RealSpace Source)) (testsBounded : UniformSchwartzBounds.Bounded tests)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (points : Set AdelicGL) (compact : IsCompact points) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ realTest ∈ tests, FourierTransform.fourier realTest 0 = 0 → ∀ point ∈ points, ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), scalarLog ≤ 0 → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp (-(power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          ‖VectorTheta.fullTheta data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation))‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := CompactPointCuspTheta.small data family continuous tests testsBounded finiteScale offset
    (finiteParameters points) (finiteParameters_compact points compact)
    (realGroup '' points) (compact.image TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedContinuity.realGroup_continuous) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun realTest testMembership zeroFourier point pointMembership integral rotation scalarLog heightLog horizontal scalarNonpositive heightNonnegative horizontalBound => ?_⟩
  rw [norm_chart, Real.exp_add, neg_mul, Real.exp_neg, Real.exp_nat_mul, ← inv_pow, Real.exp_nat_mul]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded realTest testMembership zeroFourier (realGroup point) ⟨point, pointMembership, rfl⟩ (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨⟨point, pointMembership, rfl⟩, ⟨integral, rfl⟩⟩
      (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr scalarNonpositive)


end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactVectorTheta
