module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.ProfileStage
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ExponentialTestFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.FlatProfile

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfileTestFamilies

def height (value : RealSpace) : ℝ := RealFlatProfile.height (coordinateEquiv.symm value)

theorem height_contDiffAt (value : RealSpace) (fullRank : FullRank (coordinateEquiv.symm value)) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) height value :=
  ((RealFlatProfile.height_contDiffOn.contDiffAt (fullRank_isOpen.mem_nhds fullRank)).of_le le_top).comp value
    coordinateEquiv.symm.toContinuousLinearEquiv.contDiff.contDiffAt

theorem image_parameter {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedSpace ℂ Source] [IsScalarTower ℝ ℂ Source]
    {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction)
    (finitePoint : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (map : Source →L[ℂ] data.cusp.H)
    (cutoff : Rectangular ℝ → ℝ)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value})
    (test : SchwartzMap RealSpace Source) (compact : HasCompactSupport (fun point => test point))
    (smoothHeight : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point)
    (image : ∀ value, map (test value) = cutoff (coordinateEquiv.symm value) •
      (profile (flat.1 cohomologicalPoint)
        (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding finitePoint) (coordinateEquiv.symm value))).val)
    (parameter : ℂ) (value : RealSpace) :
    map (ExponentialTestFamilies.family cohomologicalPoint height test compact smoothHeight parameter value) =
      cutoff (coordinateEquiv.symm value) •
        (profile (flat.1 parameter)
          (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding finitePoint) (coordinateEquiv.symm value))).val := by
  rw [ExponentialTestFamilies.family_apply, map_smul, image]
  by_cases fullRank : FullRank (coordinateEquiv.symm value)
  · rw [RealFlatProfile.profile_parameter flat _ ⟨finitePoint, rfl⟩ _ fullRank parameter]
    exact smul_comm _ _ _
  · have zeroCutoff : cutoff (coordinateEquiv.symm value) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun membership => fullRank (supported membership))
    rw [zeroCutoff, zero_smul, zero_smul, smul_zero]

theorem exists_family {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction)
    (finitePoint : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ indices : Finset (tsupport cutoff), ∃ radii : indices → ℝ≥0, ∃ positive : ∀ index, 0 < radii index,
      ∃ tests : ℂ → SchwartzMap RealSpace (ProductStages.Source data.cusp radii positive),
        (∀ parameter, tsupport (fun value => tests parameter value) ⊆ coordinateEquiv.symm ⁻¹' tsupport cutoff) ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (fun pair : ℂ × RealSpace => tests pair.1 pair.2) ∧
        (∀ value, Differentiable ℂ (fun parameter => tests parameter value)) ∧
        (∀ parameterSet : Set ℂ, IsCompact parameterSet → ∀ weight order : ℕ,
          ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameterSet,
            SchwartzMap.seminorm ℂ weight order (tests parameter) ≤ bound) ∧
        ∀ parameter value,
          ProductStages.hilbertMap data.cusp radii positive (tests parameter value) =
            cutoff (coordinateEquiv.symm value) •
              (profile (flat.1 parameter) (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding finitePoint)
                (coordinateEquiv.symm value))).val := by
  obtain ⟨indices, radii, positive, test, testSupport, image⟩ :=
    CompactProfileStage.exists_supported_test (flat.1 cohomologicalPoint) finitePoint cutoff smooth compact supported
  have compactSupport : HasCompactSupport (fun value => test value) :=
    (coordinateEquiv.symm.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr compact).of_isClosed_subset
      (isClosed_tsupport (fun value => test value)) testSupport
  have smoothHeight : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point :=
    fun point membership => height_contDiffAt point (supported (testSupport membership))
  let tests := ExponentialTestFamilies.family cohomologicalPoint height test compactSupport smoothHeight
  refine ⟨indices, radii, positive, tests, ?_, ?_, ?_, ?_, ?_⟩
  · intro parameter
    exact (ExponentialTestFamilies.family_support cohomologicalPoint height test compactSupport smoothHeight parameter).trans testSupport
  · exact ExponentialTestFamilies.family_joint_contDiff cohomologicalPoint height test compactSupport smoothHeight
  · exact ExponentialTestFamilies.family_pointwise_differentiable cohomologicalPoint height test compactSupport smoothHeight
  · exact ExponentialTestFamilies.family_uniform_seminorms cohomologicalPoint height test compactSupport smoothHeight
  · exact image_parameter flat finitePoint (ProductStages.hilbertMap data.cusp radii positive) cutoff supported test compactSupport smoothHeight image

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfileTestFamilies
