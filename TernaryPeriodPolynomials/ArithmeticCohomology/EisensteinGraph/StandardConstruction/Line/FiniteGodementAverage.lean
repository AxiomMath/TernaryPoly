module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.GodementAverage
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.GodementFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.ConstantTerm

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineConstantTerm

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineFiniteGodementAverage

open TernaryPeriodPolynomials.PlaneEisensteinContinuation

variable {Index : Type} {Source : Index → Type}
variable [∀ index, NormedAddCommGroup (Source index)] [∀ index, NormedSpace ℂ (Source index)]
variable [∀ index, CompleteSpace (Source index)]
variable {degree : ℕ} (data : InducingData degree) (indices : Finset Index)
variable (families : ∀ index, Source index →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
variable (tests : ∀ index, ℂ → SchwartzMap RealSpace (Source index))
variable (scales : Index → FiniteAdelesˣ) (offsets : Index → FiniteRectangularFourier.Space) (coefficients : Index → ℂ)
variable (continuous : ∀ index, Continuous (fun vector => (families index vector).val.val))
variable (holomorphic : ∀ index vector, Differentiable ℂ (fun parameter => tests index parameter vector))
variable (bounded : ∀ index, ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests index '' compact))

include continuous holomorphic bounded

theorem integrable (point : AdelicGL) (parameter : ℂ) :
    Integrable (fun pair : Adeles × Adeles => FiniteGodementFamilies.continuation data indices families tests scales offsets coefficients
      parameter (lineUnipotent pair.1 pair.2 * point)) parameterMeasure :=
  integrable_finsetSum indices (fun index _ =>
    (LineGodementAverage.integrable data (families index) (continuous index) (tests index)
      (holomorphic index) (bounded index) (scales index) (offsets index) point parameter).const_mul (coefficients index))

theorem average_sum (point : AdelicGL) (parameter : ℂ) :
    average (FiniteGodementFamilies.continuation data indices families tests scales offsets coefficients parameter) point =
      ∑ index ∈ indices, coefficients index * average (fun value => VectorGodementContinuation.continuation data
        (families index) (tests index parameter) (scales index) (offsets index) parameter value) point := by
  unfold LineConstantTerm.average FiniteGodementFamilies.continuation
  rw [integral_finsetSum indices (fun index _ =>
    (LineGodementAverage.integrable data (families index) (continuous index) (tests index)
      (holomorphic index) (bounded index) (scales index) (offsets index) point parameter).const_mul (coefficients index))]
  simp only [integral_const_mul]

theorem meromorphic (point : AdelicGL) (parameter : ℂ) :
    MeromorphicAt (fun parameter => average
      (FiniteGodementFamilies.continuation data indices families tests scales offsets coefficients parameter) point) parameter := by
  have result : MeromorphicAt (fun parameter => ∑ index ∈ indices, coefficients index *
      average (fun value => VectorGodementContinuation.continuation data (families index)
        (tests index parameter) (scales index) (offsets index) parameter value) point) parameter := by
    apply MeromorphicAt.fun_sum
    intro index _
    exact (MeromorphicAt.const (coefficients index) parameter).mul
      (LineGodementAverage.meromorphic data (families index) (continuous index) (tests index)
        (holomorphic index) (bounded index) (scales index) (offsets index) point parameter)
  exact result.congr (Filter.Eventually.of_forall (fun value =>
    (average_sum data indices families tests scales offsets coefficients continuous holomorphic bounded point value).symm))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineFiniteGodementAverage
