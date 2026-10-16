module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.ProfileRegularity
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealProfileCutoff

theorem smul_contDiff_of_support {Space Target : Type*}
    [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (cutoff : Space → ℝ) (function : Space → Target) (order : WithTop ℕ∞)
    (cutoffSmooth : ContDiff ℝ order cutoff)
    (functionSmooth : ∀ point ∈ tsupport cutoff, ContDiffAt ℝ order function point) :
    ContDiff ℝ order (fun point => cutoff point • function point) := by
  apply contDiff_iff_contDiffAt.mpr
  intro point
  by_cases inside : point ∈ tsupport cutoff
  · exact cutoffSmooth.contDiffAt.smul (functionSmooth point inside)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp inside] with value vanishing
    change cutoff value • function value = 0
    rw [show cutoff value = 0 from vanishing, zero_smul]

theorem cutoff_profile_contDiff {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL)
    (cutoff : Rectangular ℝ → ℝ) (cutoffSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (supported : tsupport cutoff ⊆ {frame : Rectangular ℝ | FullRank frame}) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun frame => cutoff frame • (profile induced (adelicFrame finitePoint frame)).val) :=
  smul_contDiff_of_support cutoff _ _ cutoffSmooth (fun frame inside =>
    (RealProfileRegularity.profile_contDiffAt induced finitePoint frame (supported inside)).of_le le_top)

def test {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL)
    (cutoff : Rectangular ℝ → ℝ) (cutoffSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {frame : Rectangular ℝ | FullRank frame}) : SchwartzMap RealSpace data.cusp.H :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinateEquiv.symm.toContinuousLinearEquiv
    ((compact.smul_right (f' := fun frame => (profile induced (adelicFrame finitePoint frame)).val)).toSchwartzMap
      (cutoff_profile_contDiff induced finitePoint cutoff cutoffSmooth supported))

theorem test_apply {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL)
    (cutoff : Rectangular ℝ → ℝ) (cutoffSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {frame : Rectangular ℝ | FullRank frame}) (value : RealSpace) :
    test induced finitePoint cutoff cutoffSmooth compact supported value =
      cutoff (coordinateEquiv.symm value) • (profile induced (adelicFrame finitePoint (coordinateEquiv.symm value))).val := rfl

theorem exists_cutoff (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ∃ cutoff : Rectangular ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff ∧ HasCompactSupport cutoff ∧
      tsupport cutoff ⊆ {frame : Rectangular ℝ | FullRank frame} ∧
      Set.range cutoff ⊆ Set.Icc 0 1 ∧ cutoff frame = 1 := by
  obtain ⟨cutoff, supported, compact, smooth, range, value⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (fullRank_isOpen.mem_nhds fullRank)
  exact ⟨cutoff, smooth, compact, supported, range, value⟩

theorem exists_test_at {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (finitePoint : FiniteGL)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ∃ realTest : SchwartzMap RealSpace data.cusp.H,
      realTest (coordinateEquiv frame) = (profile induced (adelicFrame finitePoint frame)).val := by
  obtain ⟨cutoff, smooth, compact, supported, _, value⟩ := exists_cutoff frame fullRank
  refine ⟨test induced finitePoint cutoff smooth compact supported, ?_⟩
  rw [test_apply, coordinateEquiv.symm_apply_apply, value, one_smul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealProfileCutoff
