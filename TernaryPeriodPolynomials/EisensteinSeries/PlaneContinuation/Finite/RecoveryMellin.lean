module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.PrimitiveRecovery

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealBinaryRecovery TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryMellin

theorem profile_change_parameter {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (parameter reference : ℂ)
    (finitePoint : FiniteGL) (finiteCompact : finitePoint ∈ MaximalCompact.finiteCompact)
    (value : Rectangular ℝ) (fullRank : FullRank value) :
    profile (flat.1 parameter) (adelicFrame finitePoint value) =
      Complex.exp ((parameter - reference) * (RealFlatProfile.height value : ℂ)) •
        profile (flat.1 reference) (adelicFrame finitePoint value) := by
  rw [RealFlatProfile.profile_parameter flat finitePoint finiteCompact value fullRank parameter,
    RealFlatProfile.profile_parameter flat finitePoint finiteCompact value fullRank reference, smul_smul,
    ← Complex.exp_add]
  congr 2
  ring

def realFactor (parameter reference : ℂ) (point : AdelicGL) : ℂ :=
  Complex.exp ((parameter - reference) * (RealFlatProfile.height (realFrame point) : ℂ))

theorem kernel_parameter {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (parameter reference : ℂ) (point : AdelicGL) (binary : BinaryFiniteGL) :
    kernel (flat.1 parameter) point (atFinite binary) =
      realFactor parameter reference point *
        (normPower (GeneralLinearGroup.det (atFinite binary)) (parameter - reference) *
          kernel (flat.1 reference) point (atFinite binary)) := by
  have profileEquality (key : UniversalFiniteProfiles.Key data) :
      profile (flat.1 parameter) (adelicFrame
        (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key)) (realFrame point)) =
      realFactor parameter reference point • profile (flat.1 reference) (adelicFrame
        (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key)) (realFrame point)) :=
    profile_change_parameter flat parameter reference _ ⟨UniversalFiniteProfiles.representative data key, rfl⟩
      _ (realFrame_fullRank point)
  simp only [kernel, real_mul_finite, ← realFrame_eq, profileEquality,
    FlatFrameProfile.inner_change_parameter data parameter reference, map_smul, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro key _
  ring

theorem outer_parameter {degree : ℕ} (data : InducingData degree) (parameter reference : ℂ) (scalar : Adelesˣ) :
    outerCharacter data parameter scalar = normPower scalar (-2 * (parameter - reference) / 3) *
      outerCharacter data reference scalar := by
  have exponent : -2 * inductionExponent .plane parameter =
      (-2 * (parameter - reference) / 3) + (-2 * inductionExponent .plane reference) := by
    simp only [inductionExponent]
    ring
  change data.chi.toMonoidHom scalar * normPower scalar _ = _
  rw [exponent, Helpers.normPower_add]
  unfold outerCharacter
  change _ = normPower scalar _ * (data.chi.toMonoidHom scalar * normPower scalar _)
  ring

theorem section_parameter {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (parameter reference : ℂ) (point : AdelicGL) :
    FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point =
      normPower (GeneralLinearGroup.det point) (-2 * (parameter - reference) / 3) *
        realFactor parameter reference point * outerCharacter data reference (GeneralLinearGroup.det point) *
          ∫ binary : BinaryFiniteGL,
            normPower (GeneralLinearGroup.det (atFinite binary)) (parameter - reference) *
              kernel (flat.1 reference) point (atFinite binary) ∂BinaryProductHaar.finiteMeasure := by
  simp only [FiniteRecoveryIntegral.sectionFunction, kernel_parameter flat parameter reference,
    integral_const_mul, outer_parameter data parameter reference]
  ring

theorem realHeight_orthogonal (point : AdelicGL)
    (orthogonality : (realGroup point).val.transpose * (realGroup point).val = 1) :
    RealFlatProfile.height (realFrame point) = 0 := by
  have gramEquality : GramCutoff.gram (realFrame point) = 1 := by
    rw [realFrame, ← mul_standard (realGroup point)⁻¹.val,
      GramCutoff.gram_orthogonal _ (ConstantRealMass.inverse_orthogonal (realGroup point) orthogonality),
      GramCutoff.gram_standard]
  have determinant : (RealFrameChart.completion (realFrame point)).det =
      (GramCutoff.gram (realFrame point)).det :=
    (RealFrameChart.completion_det _).trans (GramCutoff.gram_det _).symm
  rw [RealFlatProfile.height, determinant, gramEquality, Matrix.det_one, Real.log_one, neg_zero, zero_div]

theorem section_parameter_compact {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (parameter reference : ℂ) (point : AdelicGL)
    (compact : inMaximalCompact point) :
    FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point =
      outerCharacter data reference (GeneralLinearGroup.det point) *
        ∫ binary : BinaryFiniteGL,
          normPower (GeneralLinearGroup.det (atFinite binary)) (parameter - reference) *
            kernel (flat.1 reference) point (atFinite binary) ∂BinaryProductHaar.finiteMeasure := by
  rw [section_parameter flat parameter reference point]
  simp only [normPower, Height.adeleNorm_det_maximalCompact point compact, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, realFactor, realHeight_orthogonal point compact.1, one_mul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryMellin
