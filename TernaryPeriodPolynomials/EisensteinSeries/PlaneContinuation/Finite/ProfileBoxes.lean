module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegralFiniteExpansion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeCosets
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileBoxes

theorem exists_expansion {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction) (key : ℂ → RealFrame → data.cusp.smooth) :
    ∃ scale : ℚˣ, ∃ indices : Finset (Space ⧸ latticeSubgroup (FiniteLatticeMeasure.rationalScale scale)),
      ∃ coefficients : (Space ⧸ latticeSubgroup (FiniteLatticeMeasure.rationalScale scale)) → ℂ,
        ∀ point : IntegralFiniteGL,
          (∑ coset ∈ indices, coefficients coset *
            RectangularAdelicPoisson.finiteTest (FiniteLatticeMeasure.rationalScale scale) coset.out (embedding (frame point))) =
              if profileKey flat point = key then 1 else 0 := by
  obtain ⟨region, clopen, membership⟩ := CompactFiniteFrames.fiber_extension flat key
  obtain ⟨scale, indices, equality⟩ := IntegralFiniteExpansion.indicator_expansion region clopen
  refine ⟨scale, indices, fun coset => FiniteProfileCutoffs.indicator region clopen (IntegralFiniteExpansion.coordinates.symm coset.out), ?_⟩
  intro point
  rw [← equality, FiniteProfileCutoffs.indicator_embedding, membership]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileBoxes
