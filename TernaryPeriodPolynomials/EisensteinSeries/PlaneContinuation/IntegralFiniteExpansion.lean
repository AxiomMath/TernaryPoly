module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.IntegralPeriodicity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.AdelicPoisson
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ProfileCutoffs

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeCosets
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFiniteExpansion

def coordinates : Rectangular FiniteAdeles ≃ₜ Space where
  toEquiv := RectangularAdelicPoisson.coordinates.toEquiv
  continuous_toFun := continuous_pi (fun coordinate =>
    (continuous_apply coordinate.2).comp (continuous_apply coordinate.1))
  continuous_invFun := continuous_pi (fun row => continuous_pi (fun column => continuous_apply (row, column)))

theorem expansion (function : LocallyConstant (Rectangular FiniteAdeles) ℂ)
    (compact : HasCompactSupport (function : Rectangular FiniteAdeles → ℂ))
    (supported : ∀ value, value ∉ Set.range embedding → function value = 0) :
    ∃ scale : ℚˣ, ∃ indices : Finset (Space ⧸ latticeSubgroup (FiniteLatticeMeasure.rationalScale scale)),
      ∀ matrix : Rectangular FiniteAdeles, function matrix =
        ∑ coset ∈ indices, function (coordinates.symm coset.out) *
          RectangularAdelicPoisson.finiteTest (FiniteLatticeMeasure.rationalScale scale) coset.out matrix := by
  let adapted : LocallyConstant Space ℂ := LocallyConstant.comap ⟨coordinates.symm, coordinates.symm.continuous⟩ function
  have adaptedSupport : ∀ value, value ∉ Set.range FiniteIntegralPeriodicity.coordinateEmbedding → adapted value = 0 := by
    intro value outside
    apply supported
    rintro ⟨integral, equality⟩
    change embedding integral = coordinates.symm value at equality
    apply outside
    refine ⟨RectangularAdelicPoisson.coordinates integral, ?_⟩
    change coordinates (embedding integral) = value
    rw [equality, coordinates.apply_symm_apply]
  obtain ⟨scale, periodic⟩ := FiniteIntegralPeriodicity.exists_period adapted adaptedSupport
  obtain ⟨indices, equality⟩ := FiniteLatticeCosets.expansion (FiniteLatticeMeasure.rationalScale scale) adapted
    (compact.comp_homeomorph coordinates.symm) periodic
  exact ⟨scale, indices, fun matrix => equality (coordinates matrix)⟩

theorem indicator_expansion (region : Set IntegralSpace) (clopen : IsClopen region) :
    ∃ scale : ℚˣ, ∃ indices : Finset (Space ⧸ latticeSubgroup (FiniteLatticeMeasure.rationalScale scale)),
      ∀ matrix : Rectangular FiniteAdeles, FiniteProfileCutoffs.indicator region clopen matrix =
        ∑ coset ∈ indices, FiniteProfileCutoffs.indicator region clopen (coordinates.symm coset.out) *
          RectangularAdelicPoisson.finiteTest (FiniteLatticeMeasure.rationalScale scale) coset.out matrix := by
  apply expansion (FiniteProfileCutoffs.indicator region clopen)
    (FiniteProfileCutoffs.indicator_compactSupport region clopen)
  intro value outside
  rw [FiniteProfileCutoffs.indicator_apply, Set.indicator_of_notMem]
  rintro ⟨integral, _, equality⟩
  exact outside ⟨integral, equality⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFiniteExpansion
