module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.FrameHeight
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.ProfileCutoff

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatFrameProfile
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFlatProfile

def height (frame : Rectangular ℝ) : ℝ := -Real.log (RealFrameChart.completion frame).det / 2

theorem height_contDiffOn : ContDiffOn ℝ ⊤ height {frame : Rectangular ℝ | FullRank frame} :=
  ((RealFrameChart.determinant_contDiff.contDiffOn.log
    (fun frame fullRank => (completion_det_pos frame fullRank).ne')).neg).div_const 2

theorem normalized_parameter {degree : ℕ} {data : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data family)
    (finitePoint : FiniteGL) (finiteCompact : finitePoint ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) (parameter : ℂ) :
    normalized (flat.1 parameter) (atFinite finitePoint * atInfinity (point frame)) =
      Complex.exp ((parameter - cohomologicalPoint) * (height frame : ℂ)) •
        normalized (flat.1 cohomologicalPoint) (atFinite finitePoint * atInfinity (point frame)) := by
  obtain ⟨parabolic, orthogonal, factorization, orthogonality, corner⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.exists_plane_orthogonal (point frame)
  have compact : inMaximalCompact (atFinite finitePoint * atInfinity orthogonal) :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.maximalCompact.mul_mem
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact_atFinite ⟨finitePoint, finiteCompact⟩)
      ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.inMaximalCompact_atInfinity orthogonal).mpr orthogonality)
  have adelicFactorization : atFinite finitePoint * atInfinity (point frame) =
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.planeParabolicAtInfinity parabolic).val * (atFinite finitePoint * atInfinity orthogonal) := by
    rw [factorization, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, ← mul_assoc,
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, mul_assoc]
    rfl
  have logarithm : Real.log (adeleNorm (GeneralLinearGroup.det
      (planeBinaryBlock (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.planeParabolicAtInfinity parabolic))) : ℝ) = height frame := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.binaryBlock_atInfinity, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity]
    exact RealFrameHeight.binary_log frame fullRank parabolic orthogonal factorization orthogonality corner
  apply data.cusp.injective
  funext evaluation
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, adelicFactorization,
    normalized_parabolic_realize, normalized_compact flat parameter _ compact,
    inner_change_parameter data parameter cohomologicalPoint]
  rw [normPower, logarithm, mul_assoc]

theorem profile_parameter {degree : ℕ} {data : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data family)
    (finitePoint : FiniteGL) (finiteCompact : finitePoint ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) (parameter : ℂ) :
    profile (flat.1 parameter) (adelicFrame finitePoint frame) =
      Complex.exp ((parameter - cohomologicalPoint) * (height frame : ℂ)) •
        profile (flat.1 cohomologicalPoint) (adelicFrame finitePoint frame) := by
  rw [RealFrameChart.profile_eq _ _ _ fullRank, RealFrameChart.profile_eq _ _ _ fullRank]
  exact normalized_parameter flat finitePoint finiteCompact frame fullRank parameter

theorem cutoff_parameter {degree : ℕ} {data : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data family)
    (finitePoint : FiniteGL) (finiteCompact : finitePoint ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact)
    (cutoff : Rectangular ℝ → ℝ) (cutoffSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {frame : Rectangular ℝ | FullRank frame})
    (parameter : ℂ) (value : TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz.RealSpace) :
    RealProfileCutoff.test (flat.1 parameter) finitePoint cutoff cutoffSmooth compact supported value =
      Complex.exp ((parameter - cohomologicalPoint) * (height (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport.coordinateEquiv.symm value) : ℂ)) •
        RealProfileCutoff.test (flat.1 cohomologicalPoint) finitePoint cutoff cutoffSmooth compact supported value := by
  simp only [RealProfileCutoff.test_apply]
  by_cases inside : FullRank (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport.coordinateEquiv.symm value)
  · rw [profile_parameter flat finitePoint finiteCompact _ inside parameter]
    change _ • (_ • _) = _ • (_ • _)
    exact smul_comm _ _ _
  · have vanishing : cutoff (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport.coordinateEquiv.symm value) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun membership => inside (supported membership))
    rw [vanishing, zero_smul, zero_smul, smul_zero]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFlatProfile
