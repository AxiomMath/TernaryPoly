module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.ProfileStage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealStageCutoff

def test (data : CuspidalRepresentation) (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (lift : Rectangular ℝ → analyticStage data finiteCongruence radius positiveRadius)
    (domain : Set (Rectangular ℝ)) (analytic : AnalyticOnNhd ℝ lift domain)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ domain) :
    SchwartzMap RealSpace (analyticStage data finiteCongruence radius positiveRadius) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinateEquiv.symm.toContinuousLinearEquiv
    ((compact.smul_right (f' := lift)).toSchwartzMap
      (RealProfileCutoff.smul_contDiff_of_support cutoff lift _ smooth
        (fun value membership => (analytic value (supported membership)).contDiffAt)))

theorem test_apply (data : CuspidalRepresentation) (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (lift : Rectangular ℝ → analyticStage data finiteCongruence radius positiveRadius)
    (domain : Set (Rectangular ℝ)) (analytic : AnalyticOnNhd ℝ lift domain)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ domain) (value : RealSpace) :
    test data radius positiveRadius lift domain analytic cutoff smooth compact supported value =
      cutoff (coordinateEquiv.symm value) • lift (coordinateEquiv.symm value) := rfl

theorem test_hilbert {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL)
    (radius : ℝ≥0) (positiveRadius : 0 < radius)
    (lift : Rectangular ℝ → analyticStage data.cusp finiteCongruence radius positiveRadius)
    (domain : Set (Rectangular ℝ)) (analytic : AnalyticOnNhd ℝ lift domain)
    (liftValue : ∀ value ∈ domain,
      stageHilbertMap data.cusp finiteCongruence radius positiveRadius (lift value) =
        (profile induced (adelicFrame finitePoint value)).val)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ domain) (value : RealSpace) :
    stageHilbertMap data.cusp finiteCongruence radius positiveRadius
      (test data.cusp radius positiveRadius lift domain analytic cutoff smooth compact supported value) =
      cutoff (coordinateEquiv.symm value) • (profile induced (adelicFrame finitePoint (coordinateEquiv.symm value))).val := by
  rw [test_apply]
  change cutoff (coordinateEquiv.symm value) •
    stageHilbertMap data.cusp finiteCongruence radius positiveRadius (lift (coordinateEquiv.symm value)) = _
  by_cases inside : coordinateEquiv.symm value ∈ domain
  · rw [liftValue _ inside]
  · have zeroCutoff : cutoff (coordinateEquiv.symm value) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun membership => inside (supported membership)
    rw [zeroCutoff, zero_smul, zero_smul]

theorem exists_test_at {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function)
    (finitePoint : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ∃ radius : ℝ≥0, ∃ positiveRadius : 0 < radius,
      ∃ cutoff : Rectangular ℝ → ℝ,
      ∃ realTest : SchwartzMap RealSpace (analyticStage data.cusp finiteCongruence radius positiveRadius),
        ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff ∧ HasCompactSupport cutoff ∧
        tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value} ∧
        Set.range cutoff ⊆ Set.Icc 0 1 ∧ cutoff frame = 1 ∧
        ∀ value : RealSpace,
          stageHilbertMap data.cusp finiteCongruence radius positiveRadius (realTest value) =
            cutoff (coordinateEquiv.symm value) •
              (profile induced (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding finitePoint)
                (coordinateEquiv.symm value))).val := by
  obtain ⟨domain, openDomain, membership, fullRankDomain, radius, positiveRadius, lift, analytic, liftValue⟩ :=
    RealProfileStage.exists_local_lift induced finitePoint frame fullRank
  obtain ⟨cutoff, supported, compact, smooth, range, value⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (openDomain.mem_nhds membership)
  exact ⟨radius, positiveRadius, cutoff,
    test data.cusp radius positiveRadius lift domain analytic cutoff smooth compact supported,
    smooth, compact, supported.trans fullRankDomain, range, value,
    test_hilbert induced _ radius positiveRadius lift domain analytic liftValue cutoff smooth compact supported⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealStageCutoff
