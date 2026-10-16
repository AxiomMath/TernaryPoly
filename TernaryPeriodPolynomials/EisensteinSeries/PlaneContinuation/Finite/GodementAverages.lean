module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AveragedGodementContinuation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.GodementFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.ConstantTerm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteGodementAverages

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
      parameter (planeUnipotent pair.1 pair.2 * point)) parameterMeasure :=
  integrable_finsetSum indices (fun index _ =>
    (AveragedGodementContinuation.integrable data (families index) (continuous index) (tests index)
      (holomorphic index) (bounded index) (scales index) (offsets index) point parameter).const_mul (coefficients index))

theorem average_sum (point : AdelicGL) (parameter : ℂ) :
    average (FiniteGodementFamilies.continuation data indices families tests scales offsets coefficients parameter) point =
      ∑ index ∈ indices, coefficients index * average (fun value => VectorGodementContinuation.continuation data
        (families index) (tests index parameter) (scales index) (offsets index) parameter value) point := by
  unfold PlaneConstantTerm.average FiniteGodementFamilies.continuation
  rw [integral_finsetSum indices (fun index _ =>
    (AveragedGodementContinuation.integrable data (families index) (continuous index) (tests index)
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
      (AveragedGodementContinuation.meromorphic data (families index) (continuous index) (tests index)
        (holomorphic index) (bounded index) (scales index) (offsets index) point parameter)
  exact result.congr (Filter.Eventually.of_forall (fun value =>
    (average_sum data indices families tests scales offsets coefficients continuous holomorphic bounded point value).symm))

theorem average_section (point : AdelicGL) (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    average (FiniteGodementFamilies.continuation data indices families tests scales offsets coefficients parameter) point =
      VectorGodement.sectionFunction data (FiniteGodementFamilies.test data indices families tests scales offsets coefficients parameter) parameter point := by
  rw [average_sum data indices families tests scales offsets coefficients continuous holomorphic bounded point parameter,
    FiniteGodementFamilies.section_sum data indices families tests scales offsets coefficients continuous parameter point halfPlane]
  apply Finset.sum_congr rfl
  intro index _
  rw [GodementConstantTerm.average_continuation data (families index) (continuous index) (tests index parameter)
    (scales index) (offsets index) parameter halfPlane point]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteGodementAverages
