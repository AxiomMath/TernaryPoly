module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProductStages

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactProfileStage

theorem exists_supported_test {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function)
    (finitePoint : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ indices : Finset (tsupport cutoff), ∃ radii : indices → ℝ≥0, ∃ positive : ∀ index, 0 < radii index,
      ∃ realTest : SchwartzMap RealSpace (ProductStages.Source data.cusp radii positive),
        tsupport (fun value => realTest value) ⊆ coordinateEquiv.symm ⁻¹' tsupport cutoff ∧
        ∀ value : RealSpace,
          ProductStages.hilbertMap data.cusp radii positive (realTest value) =
            cutoff (coordinateEquiv.symm value) •
              (profile induced (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding finitePoint)
                (coordinateEquiv.symm value))).val := by
  have localExistence (point : tsupport cutoff) :=
    RealProfileStage.exists_local_lift induced finitePoint point.val (supported point.property)
  choose domains openDomains centerMembership fullRankDomains radii positive lifts analytic values using localExistence
  have cover : tsupport cutoff ⊆ ⋃ point : tsupport cutoff, domains point := by
    intro point membership
    exact Set.mem_iUnion.mpr ⟨⟨point, membership⟩, centerMembership ⟨point, membership⟩⟩
  obtain ⟨indices, finiteCover⟩ := compact.elim_finite_subcover domains openDomains cover
  have indexedCover : tsupport cutoff ⊆ ⋃ index : indices, domains index.val := by
    intro point membership
    obtain ⟨index, indexMembership, inside⟩ := Set.mem_iUnion₂.mp (finiteCover membership)
    exact Set.mem_iUnion.mpr ⟨⟨index, indexMembership⟩, inside⟩
  obtain ⟨test, testSupported, testValue⟩ := CompactBanachLift.exists_supported_test
    (fun index : indices => stageHilbertMap data.cusp finiteCongruence (radii index.val) (positive index.val))
    (fun point => (profile induced (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding finitePoint) point)).val)
    (fun index : indices => domains index.val) (fun index => openDomains index.val)
    (fun index : indices => lifts index.val) (fun index => analytic index.val) (fun index => values index.val)
    cutoff smooth compact indexedCover
  refine ⟨indices, (fun index => radii index.val), (fun index => positive index.val),
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinateEquiv.symm.toContinuousLinearEquiv test, ?_, ?_⟩
  · exact (tsupport_comp_subset_preimage (fun point => test point) coordinateEquiv.symm.toContinuousLinearEquiv.continuous).trans
      (Set.preimage_mono testSupported)
  intro value
  exact testValue (coordinateEquiv.symm value)

theorem exists_test {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function)
    (finitePoint : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ indices : Finset (tsupport cutoff), ∃ radii : indices → ℝ≥0, ∃ positive : ∀ index, 0 < radii index,
      ∃ realTest : SchwartzMap RealSpace (ProductStages.Source data.cusp radii positive),
        ∀ value : RealSpace,
          ProductStages.hilbertMap data.cusp radii positive (realTest value) =
            cutoff (coordinateEquiv.symm value) •
              (profile induced (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding finitePoint)
                (coordinateEquiv.symm value))).val := by
  obtain ⟨indices, radii, positive, test, _, equality⟩ := exists_supported_test induced finitePoint cutoff smooth compact supported
  exact ⟨indices, radii, positive, test, equality⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactProfileStage
