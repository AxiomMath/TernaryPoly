module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.ProfileTestFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ParametricGodementContinuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfileContinuation

theorem exists_family {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction)
    (finitePoint : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ indices : Finset (tsupport cutoff), ∃ radii : indices → ℝ≥0, ∃ positive : ∀ index, 0 < radii index,
      ∃ tests : ℂ → SchwartzMap RealSpace (ProductStages.Source data.cusp radii positive),
        (∀ parameter value,
          (ProductStages.smoothMap data.cusp radii positive (tests parameter value)).val.val =
            cutoff (coordinateEquiv.symm value) •
              (profile (flat.1 parameter) (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding finitePoint)
                (coordinateEquiv.symm value))).val) ∧
        ∀ finiteScale : FiniteAdelesˣ, ∀ offset : FiniteRectangularFourier.Space,
          IsEisensteinContinuation
            (fun parameter point => VectorGodement.sectionFunction data
              (liftTest data (ProductStages.smoothMap data.cusp radii positive)
                (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset))) parameter point)
            (fun parameter point => VectorGodementContinuation.continuation data
              (ProductStages.smoothMap data.cusp radii positive) (tests parameter) finiteScale offset parameter point) := by
  obtain ⟨indices, radii, positive, tests, _, _, holomorphic, bounded, image⟩ :=
    FlatProfileTestFamilies.exists_family flat finitePoint cutoff smooth compact supported
  refine ⟨indices, radii, positive, tests, ?_, ?_⟩
  · intro parameter value
    rw [ProductStages.smoothMap_hilbert]
    exact image parameter value
  · intro finiteScale offset
    exact ParametricGodementContinuation.isEisensteinContinuation data
      (ProductStages.smoothMap data.cusp radii positive)
      (ProductStages.smoothMap_continuous data.cusp radii positive) tests holomorphic
      (fun parameters compact => UniformSchwartzBounds.image_family tests parameters (bounded parameters compact))
      finiteScale offset

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfileContinuation
