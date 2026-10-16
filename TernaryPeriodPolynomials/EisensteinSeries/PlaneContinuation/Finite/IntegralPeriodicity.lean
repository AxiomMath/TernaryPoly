module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProfinitePeriodicity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ProfileRegularity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.LatticeCosets

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLatticeCosets
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteIntegralPeriodicity

abbrev IntegralCoordinates := Coordinate → IntegralAdeles

def coordinateEmbedding : IntegralCoordinates →+ Space where
  toFun value := fun coordinate => integralEmbedding (value coordinate)
  map_zero' := by funext coordinate; exact map_zero integralEmbedding
  map_add' first second := by funext coordinate; exact map_add integralEmbedding _ _

theorem coordinateEmbedding_continuous : Continuous coordinateEmbedding :=
  continuous_pi (fun coordinate => integralEmbedding_isOpenEmbedding.continuous.comp (continuous_apply coordinate))

theorem exists_period (function : LocallyConstant Space ℂ)
    (supported : ∀ value, value ∉ Set.range coordinateEmbedding → function value = 0) :
    ∃ scale : ℚˣ, ∀ shift ∈ latticeSubgroup (FiniteLatticeMeasure.rationalScale scale), ∀ point,
      function (shift + point) = function point := by
  obtain ⟨period, nonzero, periodic⟩ := ProfinitePeriodicity.exists_integer_period
    (fun point : IntegralCoordinates => function (coordinateEmbedding point))
    (function.isLocallyConstant.comp_continuous coordinateEmbedding_continuous)
  let scale : ℚˣ := Units.mk0 (period : ℚ) (by exact_mod_cast nonzero)
  refine ⟨scale, fun shift membership point => ?_⟩
  have coordinateMembership := (latticeSubgroup_mem (FiniteLatticeMeasure.rationalScale scale) shift).mp membership
  choose integral integralEquality using coordinateMembership
  have shiftEquality : coordinateEmbedding (period • integral) = shift := by
    funext coordinate
    have equality := integralEquality coordinate
    change ((algebraMap ℚ FiniteAdeles) (period : ℚ)) * integralEmbedding (integral coordinate) = shift coordinate at equality
    change integralEmbedding (period • integral coordinate) = shift coordinate
    rw [map_nsmul, nsmul_eq_mul]
    simpa only [map_natCast] using equality
  by_cases inside : point ∈ Set.range coordinateEmbedding
  · obtain ⟨integralPoint, rfl⟩ := inside
    rw [← shiftEquality, ← map_add]
    exact periodic integral integralPoint
  · have outside : shift + point ∉ Set.range coordinateEmbedding := by
      rintro ⟨integralPoint, equality⟩
      apply inside
      refine ⟨integralPoint - period • integral, ?_⟩
      rw [map_sub, shiftEquality, equality, add_sub_cancel_left]
    rw [supported point inside, supported (shift + point) outside]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteIntegralPeriodicity
