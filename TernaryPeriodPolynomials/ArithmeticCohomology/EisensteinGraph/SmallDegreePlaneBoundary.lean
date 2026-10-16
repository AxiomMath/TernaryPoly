module

public import TernaryPeriodPolynomials.Building.PlaneFlatExtensions
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SmallDegreeSections
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.Helpers
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.SectionAlgebra

@[expose] public section


/-! Ported from the Sol reference implementation. -/

namespace TernaryPeriodPolynomials.EisensteinGraph.SmallDegreePlaneBoundary

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open EisensteinRegularization.Helpers

theorem plane_induced_zero_of_small_degree {degree : ℕ} (small : degree < 3)
    (data : InducingData degree) (sectionValue : AdelicGL → ℂ)
    (induced : IsInduced data .plane cohomologicalPoint sectionValue) : sectionValue = 0 := by
  obtain ⟨family, flat, endpoint⟩ := PlaneFlatExtensions.plane_flat_extensions degree data sectionValue induced
  have normalized_zero := unitaryNormalize_small_degree_zero small flat.1
  funext matrix
  have value := congrFun (congrFun normalized_zero ((degree : ℂ) / 2)) matrix
  change normPower (Matrix.GeneralLinearGroup.det matrix) (-((degree : ℂ) + 3) / 3) *
    family ((degree : ℂ) / 2 - ((degree : ℂ) + 3) / 2) matrix = 0 at value
  rw [unitaryPoint_shift, endpoint] at value
  exact (mul_eq_zero.mp value).resolve_left (normPower_ne_zero _ _)

theorem plane_source_zero_of_small_degree {degree : ℕ} (small : degree < 3)
    (data : InducingData degree) (source : SourceCochain degree)
    (closed : IsSourceCocycle data .plane source) : source = 0 := by
  funext vertices matrix
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  have zero := plane_induced_zero_of_small_degree small data
    (fun argument => (source vertices argument).val.coeff monomial) (closed.1 vertices monomial)
  exact congrFun zero matrix

theorem evaluates_zero_source {degree : ℕ} (data : InducingData degree) (side : Side)
    (representative : MaximalCycles degree data.chi side)
    (evaluates : Evaluates data side 0 representative) : representative = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices flag
  induction flag using Quotient.inductionOn with
  | h matrix => exact evaluates vertices matrix

theorem plane_boundarySummand_eq_bot_of_small_degree {degree : ℕ} (small : degree < 3)
    (data : InducingData degree) : boundarySummand data .plane = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro component ⟨source, closed, representative, evaluates, rfl⟩
  have zero := plane_source_zero_of_small_degree small data source closed
  rw [zero] at evaluates
  rw [evaluates_zero_source data .plane representative evaluates, map_zero]
  exact Submodule.zero_mem _

theorem plane_boundaryClass_zero_of_small_degree {degree : ℕ} (small : degree < 3)
    (data : InducingData degree) (component : boundarySummand data .plane) : component = 0 := by
  apply Subtype.ext
  have member := component.property
  simp only [plane_boundarySummand_eq_bot_of_small_degree small data, Submodule.mem_bot] at member
  exact member

theorem zeroStandardContinuation : IsStandardContinuation 0 0 := by
  refine ⟨fun _ _ => analyticAt_const.meromorphicAt, 0, ?_⟩
  intro parameter _ matrix
  constructor
  · exact MeasureTheory.integrable_zero _ _ _
  · simp only [standardIntegrand, Pi.zero_apply, MeasureTheory.integral_zero]

theorem realizesStandard_zero_of_small_degree {degree : ℕ} (small : degree < 3)
    (data : InducingData degree) :
    RealizesStandard data (0 : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line) := by
  intro source closed representative evaluation member
  have source_zero := plane_source_zero_of_small_degree small data source closed
  refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_, 0, ?_, ?_⟩
  · intro vertices monomial
    exact PlaneEisensteinContinuation.InducedSectionAlgebra.flat_zero data
  · exact source_zero.symm
  · intro vertices monomial
    exact zeroStandardContinuation
  · intro vertices matrix monomial
    exact analyticAt_const
  · exact BadPlaneSameConstituentRepresentative.Helpers.source_cocycle_zero data .line
  · exact BadPlaneSameConstituentRepresentative.Helpers.evaluates_zero data .line
  · exact (map_zero _).symm

end TernaryPeriodPolynomials.EisensteinGraph.SmallDegreePlaneBoundary
