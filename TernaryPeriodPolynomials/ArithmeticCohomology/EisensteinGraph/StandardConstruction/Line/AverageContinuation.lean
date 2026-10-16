module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.FiniteGodementAverage
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.SectionProjection

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineAverageContinuation

def Regular (continuation : ℂ → AdelicGL → ℂ) : Prop :=
  (∀ point parameter, Integrable (fun pair : Adeles × Adeles =>
    continuation parameter (lineUnipotent pair.1 pair.2 * point)) LineConstantTerm.parameterMeasure) ∧
  ∀ point parameter, MeromorphicAt
    (fun value => LineConstantTerm.average (continuation value) point) parameter

theorem regular_mul {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation)
    (coefficient : ℂ → ℂ) (meromorphic : ∀ parameter, MeromorphicAt coefficient parameter) :
    Regular (fun parameter point => coefficient parameter * continuation parameter point) := by
  constructor
  · intro point parameter
    exact (regular.1 point parameter).const_mul _
  · intro point parameter
    simpa only [Pi.mul_def, LineConstantTerm.average, integral_const_mul] using
      (meromorphic parameter).mul (regular.2 point parameter)

theorem regular_sum {Index : Type} (indices : Finset Index)
    (continuations : Index → ℂ → AdelicGL → ℂ)
    (regular : ∀ index ∈ indices, Regular (continuations index)) :
    Regular (fun parameter point => ∑ index ∈ indices, continuations index parameter point) := by
  constructor
  · intro point parameter
    exact integrable_finsetSum indices (fun index membership => (regular index membership).1 point parameter)
  · intro point parameter
    have equality (value : ℂ) : LineConstantTerm.average
        (fun point => ∑ index ∈ indices, continuations index value point) point =
        ∑ index ∈ indices, LineConstantTerm.average (continuations index value) point :=
      integral_finsetSum indices (fun index membership => (regular index membership).1 point value)
    have result : MeromorphicAt (fun value =>
        ∑ index ∈ indices, LineConstantTerm.average (continuations index value) point) parameter :=
      MeromorphicAt.fun_sum (fun index membership => (regular index membership).2 point parameter)
    exact result.congr (Filter.Eventually.of_forall (fun value => (equality value).symm))

theorem regular_right {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation)
    (matrix : AdelicGL) : Regular (fun parameter point => continuation parameter (point * matrix)) := by
  constructor
  · intro point parameter
    simpa only [mul_assoc] using regular.1 (point * matrix) parameter
  · intro point parameter
    simpa only [LineConstantTerm.average, mul_assoc] using regular.2 (point * matrix) parameter

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
    Regular (FlatProfileInterpolation.continuation data families boxes) := by
  constructor
  · exact LineFiniteGodementAverage.integrable data Finset.univ _ _ _ _ _
      (fun index => (families index.1).continuous) (fun index => (families index.1).holomorphic)
      (fun index => (families index.1).bounded)
  · exact LineFiniteGodementAverage.meromorphic data Finset.univ _ _ _ _ _
      (fun index => (families index.1).continuous) (fun index => (families index.1).holomorphic)
      (fun index => (families index.1).bounded)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineAverageContinuation
