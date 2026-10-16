module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.ProfileAverages
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.SectionProjection

@[expose] public section


/-!
# Continuations whose constant term along the plane radical is meromorphic

`Regular continuation`: the function `u ↦ continuation s (u_P(u) g)` is integrable over the plane
radical domain and its average (the plane constant term) is meromorphic in `s`, for every `g`. The
property is stable under the operations of the recovery construction, and holds for the flat-profile
interpolations (AxiomDeep `FlatProfileAverages`). This is the plane counterpart of Sol's
`LineAverageContinuation`.

Original work by Claude Opus 5.5 (AxiomCode), adapting the Sol reference implementation
`StandardConstruction.LineAverageContinuation` from the line radical to the plane radical.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein.PlaneAverageContinuation

/-- Integrable plane radical restrictions with meromorphic plane constant term. -/
def Regular (continuation : ℂ → AdelicGL → ℂ) : Prop :=
  (∀ point parameter, Integrable (fun pair : Adeles × Adeles =>
    continuation parameter (planeUnipotent pair.1 pair.2 * point)) PlaneConstantTerm.parameterMeasure) ∧
  ∀ point parameter, MeromorphicAt
    (fun value => PlaneConstantTerm.average (continuation value) point) parameter

theorem regular_mul {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation)
    (coefficient : ℂ → ℂ) (meromorphic : ∀ parameter, MeromorphicAt coefficient parameter) :
    Regular (fun parameter point => coefficient parameter * continuation parameter point) := by
  constructor
  · intro point parameter
    exact (regular.1 point parameter).const_mul _
  · intro point parameter
    simpa only [Pi.mul_def, PlaneConstantTerm.average, integral_const_mul] using
      (meromorphic parameter).mul (regular.2 point parameter)

theorem regular_sum {Index : Type} (indices : Finset Index)
    (continuations : Index → ℂ → AdelicGL → ℂ)
    (regular : ∀ index ∈ indices, Regular (continuations index)) :
    Regular (fun parameter point => ∑ index ∈ indices, continuations index parameter point) := by
  constructor
  · intro point parameter
    exact integrable_finsetSum indices (fun index membership => (regular index membership).1 point parameter)
  · intro point parameter
    have equality (value : ℂ) : PlaneConstantTerm.average
        (fun point => ∑ index ∈ indices, continuations index value point) point =
        ∑ index ∈ indices, PlaneConstantTerm.average (continuations index value) point :=
      integral_finsetSum indices (fun index membership => (regular index membership).1 point value)
    have result : MeromorphicAt (fun value =>
        ∑ index ∈ indices, PlaneConstantTerm.average (continuations index value) point) parameter :=
      MeromorphicAt.fun_sum (fun index membership => (regular index membership).2 point parameter)
    exact result.congr (Filter.Eventually.of_forall (fun value => (equality value).symm))

theorem regular_right {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation)
    (matrix : AdelicGL) : Regular (fun parameter point => continuation parameter (point * matrix)) := by
  constructor
  · intro point parameter
    simpa only [mul_assoc] using regular.1 (point * matrix) parameter
  · intro point parameter
    simpa only [PlaneConstantTerm.average, mul_assoc] using regular.2 (point * matrix) parameter

theorem regular_average {degree : ℕ} (data : InducingData degree)
    {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation) :
    Regular (fun parameter => FiniteSectionProjection.average data (continuation parameter)) :=
  regular_mul
    (regular_sum Finset.univ _ (fun index _ => regular_right regular
      (FiniteSectionProjection.inclusion (FiniteSectionProjection.representative data index))))
    (fun _ => (Fintype.card (FiniteSectionProjection.levelImage data) : ℂ)⁻¹)
    (fun _ => analyticAt_const.meromorphicAt)

theorem flatProfile_regular {KeyType : Type} [Fintype KeyType] {degree : ℕ}
    (data : InducingData degree) (families : KeyType → FlatProfilePackages.RealFamily data)
    (boxes : KeyType → FlatProfilePackages.Boxes) :
    Regular (FlatProfileInterpolation.continuation data families boxes) :=
  ⟨fun point parameter => FlatProfileAverages.integrable data families boxes point parameter,
    fun point parameter => FlatProfileAverages.meromorphic data families boxes point parameter⟩

end TernaryPeriodPolynomials.EdgeEisenstein.PlaneAverageContinuation
